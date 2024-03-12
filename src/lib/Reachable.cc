/*
 * Reachability-based Call Graph Analysis
 *
 * Copyrigth (C) 2024 Chengyu Song
 *
 * For licensing details see LICENSE
 */


#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>

#include <algorithm>
#include <deque>
#include <fstream>
#include <vector>

#include "Reachable.h"
#include "Annotation.h"
#include "PointTo.h"

#define RA_LOG(stmt) KA_LOG(2, "Reachable: " << stmt)
#define RA_DEBUG(stmt) KA_LOG(3, "Reachable: " << stmt)

using namespace llvm;

Function* ReachableCallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getName().str());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

bool ReachableCallGraphPass::isCompatibleType(Type *T1, Type *T2) {
  if (T1 == T2) {
      return true;
#if LLVM_VERSION_MAJOR > 9
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
#endif
  } else if (T1->isIntegerTy()) {
    // assume pointer can be cased to the address space size
    if (T2->isPointerTy() && T1->getIntegerBitWidth() == T2->getPointerAddressSpace())
      return true;

    // assume all integer type are compatible
    if (T2->isIntegerTy())
      return true;
    else
      return false;
  } else if (T1->isPointerTy()) {
    if (!T2->isPointerTy())
      return false;

#if LLVM_VERSION_MAJOR > 12
    return true;
#else
    Type *ElT1 = T1->getPointerElementType();
    Type *ElT2 = T2->getPointerElementType();
    // assume "void *" and "char *" are equivalent to any pointer type
    if (ElT1->isIntegerTy(8) || ElT2->isIntegerTy(8))
      return true;

      return isCompatibleType(ElT1, ElT2);
#endif
  } else if (T1->isArrayTy()) {
    if (!T2->isArrayTy())
      return false;

    Type *ElT1 = T1->getArrayElementType();
    Type *ElT2 = T2->getArrayElementType();
    return isCompatibleType(ElT1, ElT2);
  } else if (T1->isStructTy()) {
    StructType *ST1 = cast<StructType>(T1);
    StructType *ST2 = dyn_cast<StructType>(T2);
    if (!ST2)
      return false;

    // literal has to be equal
    if (ST1->isLiteral() != ST2->isLiteral())
      return false;

    // literal, compare content
    if (ST1->isLiteral()) {
      unsigned numEl1 = ST1->getNumElements();
      if (numEl1 != ST2->getNumElements())
        return false;

      for (unsigned i = 0; i < numEl1; ++i) {
        if (!isCompatibleType(ST1->getElementType(i), ST2->getElementType(i)))
          return false;
      }
      return true;
    }

    // not literal, use name?
    return ST1->getStructName().equals(ST2->getStructName());
  } else if (T1->isFunctionTy()) {
    FunctionType *FT1 = cast<FunctionType>(T1);
    FunctionType *FT2 = dyn_cast<FunctionType>(T2);
    if (!FT2)
      return false;

    if (!isCompatibleType(FT1->getReturnType(), FT2->getReturnType()))
      return false;

    // assume varg is always compatible with varg?
    if (FT1->isVarArg()) {
      if (FT2->isVarArg())
        return true;
      else
        return false;
    }

    // compare args, again ...
    unsigned numParam1 = FT1->getNumParams();
    if (numParam1 != FT2->getNumParams())
      return false;

    for (unsigned i = 0; i < numParam1; ++i) {
      if (!isCompatibleType(FT1->getParamType(i), FT2->getParamType(i)))
        return false;
    }
    return true;
  } else if (T1->getTypeID() <= Type::FP128TyID) {
    return T1->getTypeID() == T2->getTypeID();
  } else {
    errs() << "Unhandled Types:" << *T1 << " :: " << *T2 << "\n";
    return T1->getTypeID() == T2->getTypeID();
  }
}

bool ReachableCallGraphPass::findCalleesByType(CallInst *CI, FuncSet &FS) {
#if LLVM_VERSION_MAJOR > 10
    CallBase &CS = *CI;
#else
    CallSite CS(CI);
#endif
    bool Changed = false;
    RA_LOG("Handle indirect call: " << *CI << "\n");
    for (const Function *F : Ctx->AddressTakenFuncs) {
      // just compare known args
      if (F->getFunctionType()->isVarArg()) {
        //errs() << "VarArg: " << F->getName() << "\n";
        KA_ERR("VarArg address taken function\n");
      } else if (F->arg_size() != CS.arg_size()) {
        RA_DEBUG("ArgNum mismatch: " << F->getName() << "\n");
        continue;
      } else if (!isCompatibleType(F->getReturnType(), CI->getType())) {
        RA_DEBUG("Return type mismatch: " << F->getName() << "\n");
        continue;
      }

      if (F->isIntrinsic()) {
        //errs() << "Intrinsic: " << F.getName() << "\n";
        continue;
      }

      // type matching on args
      bool Matched = true;
      auto AI = CS.arg_begin();
      for (auto FI = F->arg_begin(), FE = F->arg_end();
           FI != FE; ++FI, ++AI) {
        // check type mis-match
        Type *FormalTy = FI->getType();
        Type *ActualTy = (*AI)->getType();

        if (isCompatibleType(FormalTy, ActualTy))
          continue;
        else {
          RA_DEBUG("ArgType mismatch: " << F->getName() << " " << *FormalTy << " :: " << *ActualTy << "\n");
          Matched = false;
          break;
        }
      }

      if (Matched) {
        RA_DEBUG("Matched: " << F->getName() << "\n");
        Changed |= FS.insert(F).second;
      }
    }

    return Changed;
}

bool ReachableCallGraphPass::runOnFunction(Function *F) {
  bool Changed = false;

  RA_LOG("### Run on function: " << F->getName() << "\n");
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    
    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      if (Function *CF = CI->getCalledFunction()) {
        // direct call
        auto RCF = getFuncDef(CF);
        Changed |= Ctx->Callees[CI].insert(RCF).second;
        Changed |= Ctx->Callers[RCF].insert(CI).second;
        // check for call to exit functions
        if (isExitFn(RCF->getName())) {
          RA_LOG("Exit Call: " << *CI << "\n");
          exitBBs.insert(CI->getParent());
        }
      } else {
        // indirect call
        auto &FS = calleeByType[CI];
        Changed |= findCalleesByType(CI, FS);
        for (auto F : FS) {
          Changed |= callerByType[F].insert(CI).second;
        }
      }
    }

    // check against target list
    auto f = F->getParent()->getSourceFileName();
    auto loc = I->getDebugLoc();
    if (loc) {
      for (auto &target : targetList) {
        if (f.find(target.first) != std::string::npos && loc.getLine() == target.second) {
          RA_LOG("Target I: " << *I << "\n");
          distances[I->getParent()] = 0;
        }
      }
    }
  }
  
  return Changed;
}

bool ReachableCallGraphPass::doInitialization(Module *M) {

  for (Function &F : *M) {
    // collect address-taken functions
    if (F.hasAddressTaken()) {
      Ctx->AddressTakenFuncs.insert(&F);
      RA_LOG("AddressTaken: " << F.getName() << "\n");
    }

    // collect the exit block of the main too
    if (F.getName() == "main") {
      for (auto &BB : F) {
        if (isa<ReturnInst>(BB.getTerminator())) {
          exitBBs.insert(&BB);
        }
      }
    }
  }

  return false;
}

bool ReachableCallGraphPass::doFinalization(Module *M) {
  return false;
}

void ReachableCallGraphPass::run(ModuleList &modules) {
  ModuleList::iterator i, e;
  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    doInitialization(i->first);
  }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    for (Function &F : *i->first) {
      if (!F.isDeclaration() && !F.empty() && !F.isIntrinsic()) {
        runOnFunction(&F);
      }
    }
  }

  // do a BFS search on the call graph to find BB that can reach exits
  std::deque<BasicBlock*> worklist;
  worklist.insert(worklist.end(), exitBBs.begin(), exitBBs.end());
  while (!worklist.empty()) {
    BasicBlock *BB = worklist.front();
    worklist.pop_front();
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      BasicBlock *Pred = *PI;
      if (exitBBs.insert(Pred).second) {
        worklist.push_back(Pred);
      }
    }
    // entry block, add caller
    if (BB == &BB->getParent()->getEntryBlock()) {
      Function *F = BB->getParent();
      auto itr = Ctx->Callers.find(F);
      if (itr != Ctx->Callers.end()) {
        RA_LOG("Direct call can reach exit: " << F->getName() << "\n");
        for (auto CI : itr->second) {
          auto CBB = CI->getParent();
          if (exitBBs.insert(CBB).second) {
            worklist.push_back(CBB);
          }
        }
      } else {
        itr = callerByType.find(F);
        if (itr != callerByType.end()) {
          RA_LOG("Indirect call can reach exit: " << F->getName() << "\n");
          for (auto CI : itr->second) {
            auto CBB = CI->getParent();
            if (exitBBs.insert(CBB).second) {
              worklist.push_back(CBB);
            }
          }
        } else if (!F->getName().equals("main")) {
          WARNING("No caller for " << F->getName() << "\n");
        }
      }
    }
  }

  // now do a BFS search on the target list
  for (const auto &kv : distances)
    worklist.push_back(kv.first);
  while (!worklist.empty()) {
    BasicBlock *BB = worklist.front();
    worklist.pop_front();
    unsigned long dist = distances[BB];
    assert(dist >= 0 && "distance should not be 0");
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      BasicBlock *Pred = *PI;
      // check if the distance is already set
      auto itr = distances.find(Pred);
      if (itr == distances.end()) {
        double prob = 1.0 / std::pow(2, dist);
        assert(prob > 0.0);
        int numSucc = 0;
        for (auto SI = succ_begin(Pred), SE = succ_end(Pred); SI != SE; ++SI) {
          BasicBlock *Succ = *SI;
          numSucc++;
          if (Succ == BB) continue;
          auto itr2 = distances.find(Succ);
          if (itr2 != distances.end()) {
            prob += 1.0 / std::pow(2, itr2->second);
          }
        }
        prob /= numSucc;
        unsigned long pdist = (unsigned long)(-std::log2(prob));
        // FIXME: propagate to callee through return edge
        distances[Pred] = pdist;
        worklist.push_back(Pred);
      }
    }
    // entry block, add caller
    if (BB == &BB->getParent()->getEntryBlock()) {
      Function *F = BB->getParent();
      auto itr = Ctx->Callers.find(F);
      if (itr != Ctx->Callers.end()) {
        RA_LOG("Direct call can reach target: " << F->getName() << "\n");
        for (auto CI : itr->second) {
          auto CBB = CI->getParent();
          auto itr2 = distances.find(CBB);
          if (itr2 == distances.end()) {
            distances[CBB] = dist;
            worklist.push_back(CBB);
          }
        }
      } else {
        itr = callerByType.find(F);
        if (itr != callerByType.end()) {
          RA_LOG("Indirect call can reach target: " << F->getName() << "\n");
          for (auto CI : itr->second) {
            auto CBB = CI->getParent();
            auto itr2 = distances.find(CBB);
            if (itr2 == distances.end()) {
              // for indirect call, prob needs to be divided by the number of potential callees
              double prob = 1.0 / (1 << dist);
              prob /= calleeByType[CI].size();
              unsigned long idist = -(unsigned long)(-std::log2(prob));
              distances[CBB] = idist;
              worklist.push_back(CBB);
            }
          }
        } else if (!F->getName().equals("main")) {
          WARNING("No caller for " << F->getName() << "\n");
        }
      }
    }
  }

  for (i = modules.begin(), e = modules.end(); i != e; ++i) {
    doFinalization(i->first);
  }
}

ReachableCallGraphPass::ReachableCallGraphPass(GlobalContext *Ctx_, std::string TargetList)
  : Ctx(Ctx_) {
  // parse target list
  if (!TargetList.empty()) {
    std::ifstream ifs(TargetList);
    if (!ifs.is_open()) {
      KA_ERR("Failed to open target list file: " << TargetList);
    }
    std::string line;
    while (std::getline(ifs, line)) {
      if (line.empty() || line[0] == '#')
        continue;
      auto colon = line.find(':');
      if (colon == std::string::npos) {
        KA_ERR("Invalid target list format: " << line);
      }
      std::string f = line.substr(0, colon);
      std::string l = line.substr(colon + 1);
      int il = std::stoi(l);
      RA_LOG("Target: " << f << ":" << il << "\n");
      targetList.push_back(std::make_pair(f, il));
    }
  }
}

void ReachableCallGraphPass::dumpDistance(raw_ostream &OS) {
  // dump reachable bb
  for (const auto &kv : distances) {
    BasicBlock *BB = kv.first;
    for (auto &I : *BB) {
      auto &loc = I.getDebugLoc();
      if (loc && loc->getLine() != 0) {
        OS << loc->getFilename() << ":" << loc->getLine() << ",";
        break;
      }
    }
    OS << kv.second << "\n";
  }

  // dump unreachable bb
  for (auto BB : exitBBs) {
    if (distances.find(BB) == distances.end()) {
      for (auto &I : *BB) {
        auto &loc = I.getDebugLoc();
        if (loc) {
          OS << loc->getFilename() << ":" << loc->getLine() << ",";
          break;
        }
      }
      OS << "inf\n";
    }
  }
}

void ReachableCallGraphPass::dumpCallees() {
    RES_REPORT("\n[dumpCallees]\n");
    raw_ostream &OS = outs();
    OS << "Num of Callees: " << calleeByType.size() << "\n";
    for (CalleeMap::iterator i = calleeByType.begin(),
         e = calleeByType.end(); i != e; ++i) {

        auto CI = i->first;
        FuncSet &v = i->second;
        // only dump indirect call?
        if (CI->isInlineAsm() || CI->getCalledFunction() /*|| v.empty()*/)
             continue;

        // OS << "CS:" << *CI << "\n";
        // const DebugLoc &LOC = CI->getDebugLoc();
        // OS << "LOC: ";
        // LOC.print(OS);
        // OS << "^@^";
        std::string prefix = "<" + CI->getParent()->getParent()->getParent()->getName().str() + ">"
            + CI->getParent()->getParent()->getName().str() + "::";
#if 1
        for (FuncSet::iterator j = v.begin(), ej = v.end();
             j != ej; ++j) {
            //OS << "\t" << ((*j)->hasInternalLinkage() ? "f" : "F")
            //    << " " << (*j)->getName() << "\n";
            OS << prefix << *CI << "\t";
            OS << (*j)->getName() << "\n";
        }
#endif
        // OS << "\n";

        // v = Ctx->Callees[CI];
        // OS << "Callees: ";
        // for (FuncSet::iterator j = v.begin(), ej = v.end();
        //      j != ej; ++j) {
        //     OS << (*j)->getName() << "::";
        // }
        // OS << "\n";
        if (v.empty()) {
#if LLVM_VERSION_MAJOR > 10
            OS << "!!EMPTY =>" << *CI->getCalledOperand()<<"\n";
#else
            OS << "!!EMPTY =>" << *CI->getCalledValue()<<"\n";
#endif
            OS<< "Uninitialized function pointer is dereferenced!\n";
        }
    }
    RES_REPORT("\n[End of dumpCallees]\n");
}

void ReachableCallGraphPass::dumpCallers() {
    RES_REPORT("\n[dumpCallers]\n");
    for (auto M : Ctx->Callers) {
        const Function *F = M.first;
        CallInstSet &CIS = M.second;
        RES_REPORT("F : " << getScopeName(F) << "\n");

        for (auto *CI : CIS) {
            auto CallerF = CI->getParent()->getParent();
            RES_REPORT("\t");
            if (CallerF && CallerF->hasName()) {
                RES_REPORT("(" << getScopeName(CallerF) << ") ");
            } else {
                RES_REPORT("(anonymous) ");
            }

            RES_REPORT(*CI << "\n");
        }
    }
    RES_REPORT("\n[End of dumpCallers]\n");
}
