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
#include <cassert>
#include <iomanip>
#include <fstream>
#include <vector>

#include "Reachable.h"
#include "Annotation.h"
#include "PointTo.h"

#define RA_LOG(stmt) KA_LOG(2, "Reachable: " << stmt)
#define RA_DEBUG(stmt) KA_LOG(3, "Reachable: " << stmt)

using namespace llvm;

Function* ReachableCallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getGUID());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

bool ReachableCallGraphPass::isCompatibleType(Type *T1, Type *T2) {
  if (T1 == T2) {
      return true;
  } else if (T1->isVoidTy()) {
    return T2->isVoidTy();
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
    CallBase &CS = *CI;
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
          RA_DEBUG("Adding indirect caller for " << F->getName() << "@" << F << "\n");
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
          distances[I->getParent()] = 0.0;
          reachableBBs.insert(I->getParent());
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
      RA_LOG("AddressTaken: " << F.getName() << "\n");
      // hmmm, turns out F can be declaration
      auto RF = getFuncDef(&F);
      if (F.getFunctionType()->isVarArg()) {
        RA_DEBUG("  VarArg: " << F.getName() << "\n");
      } else {
        Ctx->AddressTakenFuncs.insert(RF);
      }
    }

    // collect the exit block of the main too
    if (F.getName() == "main") {
      entryBBs.insert(&F.getEntryBlock());
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

void ReachableCallGraphPass::collectReachable(std::deque<const BasicBlock*> &worklist, std::unordered_set<const BasicBlock*> &reachable) {
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      auto *Pred = *PI;
      if (reachable.insert(Pred).second) {
        worklist.push_back(Pred);
      }
    }
    // entry block, add caller
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      auto itr = Ctx->Callers.find(F);
      if (itr != Ctx->Callers.end()) {
        RA_DEBUG("Direct call can reach: " << F->getName() << "\n");
        for (auto CI : itr->second) {
          auto CBB = CI->getParent();
          if (reachable.insert(CBB).second) {
            worklist.push_back(CBB);
          }
        }
      } else {
        itr = callerByType.find(F);
        if (itr != callerByType.end()) {
          RA_DEBUG("Indirect call can reach: " << F->getName() << "\n");
          for (auto CI : itr->second) {
            auto CBB = CI->getParent();
            if (reachable.insert(CBB).second) {
              worklist.push_back(CBB);
            }
          }
        } else if (!F->getName().equals("main")) {
          WARNING("No caller for " << F->getName() << "\n");
        }
      }
    }
  }
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
  std::deque<const BasicBlock*> worklist;
  RA_DEBUG("=== Collecting exit BBs ===\n");
  worklist.insert(worklist.end(), exitBBs.begin(), exitBBs.end());
  collectReachable(worklist, exitBBs);

  // now do a BFS search on the target list, find all reachable BBs first
  RA_DEBUG("=== Collecting reachable BBs ===\n");
  for (const auto &kv : distances)
    worklist.push_back(kv.first);
  collectReachable(worklist, reachableBBs);

  // now calculate distances in a bottom-up manner
  for (const auto &kv : distances)
    worklist.push_back(kv.first);
  // fixed point iteration?
  while (!worklist.empty()) {
    auto *BB = worklist.front();
    worklist.pop_front();
    // check predecessors
    for (auto PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      auto *Pred = *PI;
      int numSucc = 0;
      double prob = 0.0;
      for (auto SI = succ_begin(Pred), SE = succ_end(Pred); SI != SE; ++SI) {
        auto *Succ = *SI;
        numSucc++;
        // unreachable one has prob 0
        if (reachableBBs.find(Succ) == reachableBBs.end())
          continue;
        auto itr = distances.find(Succ);
        if (itr != distances.end()) {
          prob += 1.0 / std::pow(2, itr->second);
        }
      }
      prob /= numSucc;
      auto dist = (-std::log2(prob));
      // FIXME: propagate to callee through return edge
      auto itr = distances.find(Pred);
      if (itr == distances.end() || itr->second != dist) {
        // RA_DEBUG("Adding Pred: " << *Pred << " with prob " << prob << "\n");
        distances[Pred] = dist;
        worklist.push_back(Pred);
      }
    }
    // entry block has no predecessor, add caller
    auto *F = BB->getParent();
    if (BB == &F->getEntryBlock()) {
      auto itr = Ctx->Callers.find(F);
      if (itr != Ctx->Callers.end()) {
        RA_LOG("Direct call can reach target: " << F->getName() << "\n");
        // for direct calls, prob can be propagated directly
        auto dist = distances[BB];
        for (auto CI : itr->second) {
          auto CBB = CI->getParent();
          auto itr2 = distances.find(CBB);
          if (itr2 == distances.end() || itr2->second != dist) {
            RA_DEBUG("Adding caller: " << CI->getFunction()->getName() << "\n");
            distances[CBB] = dist;
            worklist.push_back(CBB);
          }
        }
      } else {
        // indirect call is tricky, treat like predecessors
        itr = callerByType.find(F);
        if (itr != callerByType.end()) {
          RA_LOG("Indirect call can reach target: " << F->getName() << "\n");
          for (auto CI : itr->second) {
            auto CBB = CI->getParent();
            auto old = distances[CBB];
            // for each call site, check if all its callees have been processed
            int numCallees = 0;
            double prob = 0.0;
            for (auto F : calleeByType[CI]) {
              numCallees++;
              auto CEBB = const_cast<BasicBlock*>(&F->getEntryBlock());
              if (reachableBBs.find(CEBB) == reachableBBs.end()) {
                continue;
              }
              auto itr2 = distances.find(CEBB);
              if (itr2 != distances.end()) {
                prob += 1.0 / std::pow(2, itr2->second);
              }
            }
            // for indirect call, prob needs to be divided by the number of potential callees
            prob /= numCallees;
            auto dist = (-std::log2(prob));
            if (old != dist) {
              RA_DEBUG("Adding indirect caller: " << CI->getFunction()->getName() << "\n");
              distances[CBB] = dist;
              worklist.push_back(CBB);
            }
          }
        } else if (!F->getName().equals("main")) {
          WARNING("No caller for " << F->getName() << "@" << F << "\n");
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

void ReachableCallGraphPass::dumpDistance(raw_ostream &OS, bool dumpSolution, bool dumpUnreachable) {
  std::deque<const BasicBlock*> worklist;
  std::unordered_set<const BasicBlock*> visited;
  unsigned long currentDist = -1;
  for (auto BB : entryBBs) {
    if (distances.find(BB) != distances.end()) {
      RA_LOG("Entry BB of " << BB->getParent()->getName() << " is reachable\n");
      worklist.push_back(BB);
      visited.insert(BB);
    }
  }
  if (worklist.empty()) {
    WARNING("Target not reachable from entry BBs\n");
    return;
  }
  // dump reachable bb
  if (dumpSolution) {
    while (!worklist.empty()) {
      auto *BB = worklist.front();
      worklist.pop_front();
      if (distances[BB] < currentDist) {
        currentDist = distances[BB];
        RA_DEBUG("Best option: " << BB->getParent()->getName() << " at " << currentDist << "\n");
      }
      bool printed = false;
      for (auto &I : *BB) {
        if (!printed) {
          auto &loc = I.getDebugLoc();
          if (loc && loc->getLine() != 0) {
            auto f = loc->getFilename();
            if (f.empty()) {
              f = BB->getParent()->getParent()->getSourceFileName();
            }
            if (f.find("./") == 0) {
              f = f.substr(2);
            }
            OS << f << ":" << loc->getLine() << ",";
            std::ostringstream formattedDistance;
            formattedDistance << std::fixed << std::setprecision(6) << distances[BB] * 1000;
            OS << formattedDistance.str() << "\n";
            printed = true;
          }
        }
        // check for callees
        if (const CallInst *CI = dyn_cast<CallInst>(&I)) {
          auto itr = Ctx->Callees.find(CI);
          if (itr == Ctx->Callees.end()) {
            itr = calleeByType.find(CI);
          }
          for (auto F: itr->second) {
            auto *FBB = &F->getEntryBlock();
            if (distances.find(FBB) != distances.end() && visited.insert(FBB).second) {
              worklist.push_back(FBB);
            }
          }
        }
      }
      for (auto SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
        auto *Succ = *SI;
        if (distances.find(Succ) != distances.end() && visited.insert(Succ).second) {
          worklist.push_back(Succ);
        }
      }
    }
  } else {
    for (const auto &kv : distances) {
      auto *BB = kv.first;
      auto term = BB->getTerminator();
      auto branch = dyn_cast<BranchInst>(term);
      if (!branch || !branch->isConditional())
        continue;
      auto TT = branch->getSuccessor(0);
      auto FT = branch->getSuccessor(1);
      OS << getBasicBlockId(BB) << ",";
      auto itr = distances.find(FT);
      if (itr != distances.end()) {
        std::ostringstream formattedDistance;
        formattedDistance << std::fixed << std::setprecision(6) << itr->second * 1000;
        OS << formattedDistance.str() << ",";
      } else {
        OS << "inf,";
      }
      itr = distances.find(TT);
      if (itr != distances.end()) {
        std::ostringstream formattedDistance;
        formattedDistance << std::fixed << std::setprecision(6) << itr->second * 1000;
        OS << formattedDistance.str() << "\n";
      } else {
        OS << "inf\n";
      }
    }
  }

  // dump unreachable bb
  if (dumpUnreachable) {
    for (auto BB : exitBBs) {
      if (distances.find(BB) == distances.end()) {
        for (auto &I : *BB) {
          auto &loc = I.getDebugLoc();
          if (loc && loc->getLine() != 0) {
            auto f = loc->getFilename();
            if (f.empty()) {
              f = BB->getParent()->getParent()->getSourceFileName();
            }
            if (f.find("./") == 0) {
              f = f.substr(2);
            }
            OS << f << ":" << loc->getLine() << ",";
            break;
          }
        }
        OS << "inf\n";
      }
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
