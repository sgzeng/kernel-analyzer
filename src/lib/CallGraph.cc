/*
 * Call graph construction
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 - 2016 Chengyu Song 
 * Copyright (C) 2016 Kangjie Lu
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

#include <vector>
#include <algorithm>

#include "CallGraph.h"
#include "Annotation.h"
#include "PointTo.h"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)

using namespace llvm;

Function* CallGraphPass::getFuncDef(Function *F) {
  FuncMap::iterator it = Ctx->Funcs.find(F->getName().str());
  if (it != Ctx->Funcs.end())
    return it->second;
  else
    return F;
}

bool CallGraphPass::isCompatibleType(Type *T1, Type *T2) {
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
    return isCompatibleType(ElT1, ElT1);
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

bool CallGraphPass::findCalleesByType(CallInst *CI, FuncSet &FS) {
#if LLVM_VERSION_MAJOR > 10
    CallBase &CS = *CI;
#else
    CallSite CS(CI);
#endif
    //errs() << *CI << "\n";
    for (const Function *F : Ctx->AddressTakenFuncs) {

        // just compare known args
        if (F->getFunctionType()->isVarArg()) {
            //errs() << "VarArg: " << F->getName() << "\n";
            //report_fatal_error("VarArg address taken function\n");
        } else if (F->arg_size() != CS.arg_size()) {
            //errs() << "ArgNum mismatch: " << F.getName() << "\n";
            continue;
        } else if (!isCompatibleType(F->getReturnType(), CI->getType())) {
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
                Matched = false;
                break;
            }
        }

        if (Matched)
            FS.insert(F);
    }

    return false;
}

#if LLVM_VERSION_MAJOR > 10
bool CallGraphPass::handleCall(llvm::CallBase *CS, const llvm::Function *CF,
                               SmallVectorImpl<Instruction*> &worklist, bool &Changed) {
#else
bool CallGraphPass::handleCall(llvm::CallInst *CS, const llvm::Function *CF,
                               SmallVectorImpl<Instruction*> &worklist, bool &Changed) {
#endif
  if (CF->isIntrinsic())
    return false;

  // assumes CF is the function definition
  if (CF->empty()) {
    // external function, nothing to do
    return false;
  }

  // handle args
  unsigned numArgs = CS->arg_size();
  if (CF->isVarArg()) {
    NodeIndex formalNode = NF.getVarargNodeFor(CF);
    assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (funcPts.find(arg) == funcPts.end()) continue;
      NodeIndex argNode = NF.getValueNodeFor(arg);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      auto itr = funcPtsGraph.find(argNode);
      assert(itr != funcPtsGraph.end() && "Actual argument node not found in the graph!");
      if (funcPtsGraph[formalNode].insert(itr->second) > 0) {
        CG_LOG("VarArg: (" << i << ") " << *CS << " -> " << CF->getName() << "\n");
      }
    }
  } else {
    assert(numArgs == CF->arg_size() && "Call argument number mismatch!");
    for (unsigned i = 0; i < numArgs; i++) {
      Value *arg = CS->getArgOperand(i);
      if (funcPts.find(arg) == funcPts.end()) continue;
      NodeIndex argNode = NF.getValueNodeFor(arg);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Actual argument node not found!");
      auto itr = funcPtsGraph.find(argNode);
      if (itr != funcPtsGraph.end()) {
        Value *farg = CF->getArg(i);
        NodeIndex formalNode = NF.getValueNodeFor(farg);
        assert(formalNode != AndersNodeFactory::InvalidIndex && "Formal argument node not found!");
        if (funcPtsGraph[formalNode].insert(itr->second) > 0) {
          CG_LOG("Arg: (" << i << ") " << *CS << " -> " << CF->getName() << "\n");
          // add the formal node to the workset
          _workset.insert(farg);
          funcPts.insert(farg);
          Changed = true;
        }
      } else if (funcPts.find(arg) != funcPts.end()) {
        // we are expecting point2 from the actual argument
        CG_LOG("Call: (" << i << ") " << *CS << " actual argument node not found in the graph: " << *arg << "\n");
        Changed |= findDefinitions(arg, worklist);
      }
    }
  }

  // handle return
  bool ret = false;
  if (!CF->getReturnType()->isVoidTy()) {
    NodeIndex retNode = NF.getReturnNodeFor(CF);
    assert(retNode != AndersNodeFactory::InvalidIndex && "Return node not found!");
    NodeIndex callNode = NF.getValueNodeFor(CS);
    assert(callNode != AndersNodeFactory::InvalidIndex && "Call node not found!");
    auto itr = funcPtsGraph.find(retNode);
    if (itr != funcPtsGraph.end()) {
      // if the point2 set of the return is not empty
      // XXX: special handling for returned pts
      for (auto idx = itr->second.find_first(), end = itr->second.getSize();
           idx < end; idx = itr->second.find_next(idx)) {
        // if the obj is a heap obj and has no type, treating the CF as an allocator
        // and create a new heap obj
        if (NF.isHeapObject(idx) && NF.isOpaqueObject(idx) && CF->getName().find("alloc") != StringRef::npos) {
          idx = NF.createOpaqueObjectNode(CS, true);
          WARNING("Call: treating " << CF->getName() << " as an allocator (" << idx << ")\n");
        }
        ret |= funcPtsGraph[callNode].insert(idx);
      }
    } else if (funcPts.find(CS) != funcPts.end()) {
      // we are expecting point2 from the return value
      CG_LOG("Call: " << *CS << " return node not found in the graph: " << CF->getName() << "\n");
      // add the return inst to the workset
      for (auto &BB : *CF) {
        if (auto *I = dyn_cast<ReturnInst>(BB.getTerminator())) {
          CG_LOG("Tracing Return: " << *I << "\n");
          ReturnInst *RI = const_cast<ReturnInst*>(I);
          _workset.insert(RI);
          funcPts.insert(RI->getReturnValue());
        }
      }
      Changed = true;
    }
  }

  return ret;
}

bool CallGraphPass::findDefinitions(Value *ptr, SmallVectorImpl<Instruction*> &worklist) {
  // point2 of ptr has not been resolved yet
  if (Instruction *PI = dyn_cast<Instruction>(ptr)) {
    // if ptr is from a local instruction, add it to the worklist
    worklist.push_back(PI);
  } else if (Argument *A = dyn_cast<Argument>(ptr)) {
    // if ptr is from an argument, add the actual argument to the workset
    if (funcPts.find(A) != funcPts.end()) {
      Function *F = A->getParent();
      for (auto CS : Ctx->Callers[F]) {
        auto argNum = A->getArgNo();
        Value *arg = CS->getArgOperand(argNum);
        Function *CF = CS->getParent()->getParent();
        CG_LOG("Tracing Arg Ptr: " << *CS << " <- " << CF->getName() << ":" << argNum << "\n");
        _workset.insert(CS);
        funcPts.insert(arg);
      }
      return true;
    }
  } else {
    WARNING("Unhandled ptr source: " << *ptr << "\n");
  }

  return false;
}

static inline Type *getElementTy(Type *T) {
  while (T) {
    if (ArrayType *AT = dyn_cast<ArrayType>(T))
      T = AT->getElementType();
    else if (VectorType *VT = dyn_cast<VectorType>(T))
      T = VT->getElementType();
    else
      break;
  }

  return T;
}

bool CallGraphPass::runOnFunction(Function *F) {
  bool Changed = false;

  SmallVector<Instruction*, 32> worklist;

  // collect from arguments
  for (Argument &A : F->args()) {
    if (_workset.find(&A) != _workset.end()) {
      _workset.erase(&A);
      NodeIndex argNode = NF.getValueNodeFor(&A);
      assert(argNode != AndersNodeFactory::InvalidIndex && "Argument node not found!");
      auto itr = funcPtsGraph.find(argNode);
      assert(itr != funcPtsGraph.end() && "Argument node not found in the graph!");
      for (User *U : A.users()) {
        if (Instruction *UI = dyn_cast<Instruction>(U)) {
          worklist.push_back(UI);
        }
      }
    }
  }

  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;

    if (_workset.find(I) == _workset.end())
      continue;
    _workset.erase(I);
    worklist.push_back(I);
  }

  if (worklist.empty())
    return Changed;

  CG_LOG("######\nProcessing Func: " << F->getName() << "\n");

  // FIXME: reverse the worklist?
  std::reverse(worklist.begin(), worklist.end());

  while (!worklist.empty()) {
    Instruction *I = worklist.pop_back_val();

    CG_LOG("Processing instruction: " << *I << "\n");
    // propagate function pointer assignments
    bool propagated = false;
    switch (I->getOpcode()) {
    case Instruction::Ret: {
      if (I->getNumOperands() > 0) {
        Value *rv = I->getOperand(0);
        NodeIndex rvNode = NF.getValueNodeFor(rv);
        assert(rvNode != AndersNodeFactory::InvalidIndex && "Return value node not found!");
        auto itr = funcPtsGraph.find(rvNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the return value is not empty
          NodeIndex RT = NF.getReturnNodeFor(F);
          assert(RT != AndersNodeFactory::InvalidIndex && "Return node not found!");
          if (funcPtsGraph[RT].insert(itr->second) > 0) {
            CG_LOG("Ret: " << *I << " <- " << F->getName() << "\n");
            // add callsites to the workset
            for (auto CS: Ctx->Callers[F]) {
              _workset.insert(CS);
              funcPts.insert(CS);
            }
            Changed = true;
          }
        } else if (funcPts.find(rv) != funcPts.end()) {
          CG_LOG("Ret: " << *I << " return value node not found in the graph: " << *rv << "\n");
          Changed |= findDefinitions(rv, worklist);
        }
      }
      break;
    }
#if LLVM_VERSION_MAJOR > 10
    case Instruction::Invoke:
    case Instruction::Call: {
      CallBase *CS = cast<CallBase>(I);
#else
    case Instruction::Call: {
      CallInst *CS = cast<CallInst>(I);
#endif
      if (CS->isInlineAsm()) break;
      if (Function *CF = CS->getCalledFunction()) {
        // direct call
        propagated = handleCall(CS, getFuncDef(CF), worklist, Changed);
        break;
      }
      // indirect call
      Value *CO = CS->getCalledOperand();
      NodeIndex callee = NF.getValueNodeFor(CO);
      assert(callee != AndersNodeFactory::InvalidIndex && "Callee node not found!");
      auto itr = funcPtsGraph.find(callee);
      // iterate through all possible callees
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the callee is not empty
        for (auto idx = itr->second.find_first(), end = itr->second.getSize();
             idx < end; idx = itr->second.find_next(idx)) {
          CG_LOG("Indirect Call: callee obj: " << idx << "\n");
          if (NF.isSpecialNode(idx)) {
            WARNING("Indirect Call: " << *CO << " callee is a special node: " << idx << "\n")
            continue;
          }
          assert(NF.isObjectNode(idx) && "Function pointer points to non-object!");
          const Value *CV = NF.getValueForNode(idx);
          assert(CV != NULL && "No value for function node!");
          const Function *CF = dyn_cast<Function>(CV);
          if (CF == NULL) {
            KA_ERR("Function pointer " << *CO << " points to non-function: " << *CV << "\n");
          }
          CG_LOG("Indirect Call: callee: " << CF->getName() << "\n");
          propagated |= handleCall(CS, CF, worklist, Changed);
          // update callers
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CS);
        }
      }
      break;
    }
    case Instruction::Alloca: {
      // alloca should only be in the worklist for tracing back ptr defs,
      // so we only care about the store users
      for (User *U : I->users()) {
        if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
          worklist.push_back(SI);
          funcPts.insert(SI->getValueOperand());
        }
      }
      break;
    }
    case Instruction::Load: {
      Value *ptr = I->getOperand(0);
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      NodeIndex valNode = NF.getValueNodeFor(I);
      auto itr = funcPtsGraph.find(ptrNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        for (auto idx = itr->second.find_first(), end = itr->second.getSize();
             idx < end; idx = itr->second.find_next(idx)) {
          // for every obj the source ptr points to, propagate the func ptrs
          CG_LOG("Load: source obj: " << idx << "\n");
          auto itr2 = funcPtsGraph.find(idx);
          if (itr2 != funcPtsGraph.end()) {
#if 1
            for (auto idx2 = itr2->second.find_first(), end2 = itr2->second.getSize();
                 idx2 < end2; idx2 = itr2->second.find_next(idx2)) {
              CG_LOG("Load: insert: " << idx2 << "\n");
              propagated |= funcPtsGraph[valNode].insert(idx2);
            }
#else
            propagated |= (funcPtsGraph[valNode].insert(itr2->second) > 0);
#endif
          }
        }
      }
      itr = funcPtsGraph.find(valNode);
      if ((itr == funcPtsGraph.end()) && (funcPts.find(I) != funcPts.end())) {
        // we are expecting point2 from the loaded value
        CG_LOG("Load: pointer operand not found in the graph: " << ptrNode << "\n");
        Changed |= findDefinitions(ptr, worklist);
      }
      break;
    }
    case Instruction::Store: {
      Value *val = I->getOperand(0);
      Value *ptr = I->getOperand(1);
      NodeIndex valNode = NF.getValueNodeFor(val);
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      auto itr = funcPtsGraph.find(valNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the value is not empty, i.e., a ptr
        // for every obj the dst ptr points to, propagate the func ptrs
        auto itr2 = funcPtsGraph.find(ptrNode);
        if (itr2 != funcPtsGraph.end()) {
          for (auto idx = itr2->second.find_first(), end = itr2->second.getSize();
              idx < end; idx = itr2->second.find_next(idx)) {
            CG_LOG("Store: dst obj: " << idx << "\n");
            if (NF.isSpecialNode(idx)) continue;
            if (funcPtsGraph[idx].insert(itr->second) > 0) {
              // for store, we want to add the load users of the dst ptr to the workset
              for (User *U : ptr->users()) {
                if (LoadInst *LI = dyn_cast<LoadInst>(U)) {
                  worklist.push_back(LI);
                }
              }
              // conservatively set the changed flag if the dst ptr is a heap obj
              Changed |= NF.isHeapObject(idx);
            }
          }
        } else {
          // we know the value node can reach a func ptr, but the dst ptr is not in the graph
          CG_LOG("Store: pointer operand not found in the graph: " << ptrNode << "\n");
          funcPts.insert(ptr);
          Changed |= findDefinitions(ptr, worklist);
        }
      } else if (funcPts.find(val) != funcPts.end()) {
        // we are expecting point2 from the stored value
        CG_LOG("Store: value operand not found in the graph: " << valNode << "\n");
        Changed |= findDefinitions(val, worklist);
      }
      break;
    }
    case Instruction::GetElementPtr: {
      GetElementPtrInst *GEP = cast<GetElementPtrInst>(I);
      Value *ptr = GEP->getPointerOperand();
      Type *ptrTy = getElementTy(GEP->getSourceElementType());
      NodeIndex ptrNode = NF.getValueNodeFor(ptr);
      NodeIndex valNode = NF.getValueNodeFor(I);

      auto itr = funcPtsGraph.find(ptrNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        for (auto idx = itr->second.find_first(), end = itr->second.getSize();
             idx < end; idx = itr->second.find_next(idx)) {

          CG_LOG("GEP source obj " << idx << "\n");
          if (NF.isSpecialNode(idx)) {
            // special object, e.g., null or univeral
            propagated |= funcPtsGraph[valNode].insert(idx);
            continue;
          }

          // check if we need to resize the obj of the ptr
          if (StructType *STy = dyn_cast<StructType>(ptrTy)) {
            const StructInfo* stInfo = SA.getStructInfo(STy, F->getParent());
            assert(stInfo != NULL && "Struct info not found!");
            unsigned ptrSize = stInfo->getExpandedSize();
            // get allocated size
            unsigned allocSize = NF.getObjectSize(idx);
            if (NF.isOpaqueObject(idx) || ptrSize > allocSize) {
              CG_LOG("GEP resize obj: " << idx << " to type " << STy->getName() << "\n");
              // resize the obj
              idx = extendObjectSize(idx, STy, NF, SA, funcPtsGraph);
            }
          }

          // get the field number
          const DataLayout* DL = &(F->getParent()->getDataLayout());
          unsigned fieldNum = 0;
          int64_t offset = getGEPOffset(GEP, DL);
          if (offset < 0) {
            // FIXME: handle negative offset, like container_of
            WARNING("GEP: " << *I << " negative offset: " << offset << "\n");
            break;
          } else {
            fieldNum = offsetToFieldNum(GEP->getSourceElementType(), offset, DL, SA, F->getParent());
          }
          CG_LOG("GEP fieldNum: " << fieldNum << "\n");

          // propagate the ptr info
          propagated |= funcPtsGraph[valNode].insert(idx + fieldNum);
        }
      } else if (funcPts.find(I) != funcPts.end()) {
        // we are expecting point2 from the resulting ptr
        CG_LOG("GEP: pointer operand not found in the graph: " << ptrNode << "\n");
        funcPts.insert(ptr);
        Changed |= findDefinitions(ptr, worklist);
      }
      break;
    }
    case Instruction::BitCast: {
      NodeIndex srcNode = NF.getValueNodeFor(I->getOperand(0));
      assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find bitcast src node");
      auto itr = funcPtsGraph.find(srcNode);
      if (itr != funcPtsGraph.end()) {
        // if the point2 set of the source ptr is not empty
        NodeIndex dstNode = NF.getValueNodeFor(I);
        propagated |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
      } else if (funcPts.find(I) != funcPts.end()) {
        // we are expecting point2 from the resulting ptr
        CG_LOG("BitCast: src node not found in the graph: " << srcNode << "\n");
        funcPts.insert(I->getOperand(0));
        Changed |= findDefinitions(I->getOperand(0), worklist);
      }
      break;
    }
    case Instruction::ICmp: {
      // do nothing
      break;
    }
    case Instruction::PHI: {
      PHINode* PHI = cast<PHINode>(I);
      NodeIndex dstNode = NF.getValueNodeFor(PHI);
      for (unsigned i = 0, e = PHI->getNumIncomingValues(); i != e; ++i) {
        NodeIndex srcNode = NF.getValueNodeFor(PHI->getIncomingValue(i));
        assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find phi src node");
        auto itr = funcPtsGraph.find(srcNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the source ptr is not empty
          propagated |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
        } else if (funcPts.find(PHI) != funcPts.end()) {
          // we are expecting point2 from the resulting ptr
          CG_LOG("PHI: src node not found in the graph: " << srcNode << "\n");
          funcPts.insert(PHI->getIncomingValue(i));
          Changed |= findDefinitions(PHI->getIncomingValue(i), worklist);
        }
      }
      break;
    }
    case Instruction::Select: {
      NodeIndex dstNode = NF.getValueNodeFor(I);
      for (unsigned i = 1; i < I->getNumOperands(); i++) {
        NodeIndex srcNode = NF.getValueNodeFor(I->getOperand(i));
        assert(srcNode != AndersNodeFactory::InvalidIndex && "Failed to find select src node");
        auto itr = funcPtsGraph.find(srcNode);
        if (itr != funcPtsGraph.end()) {
          // if the point2 set of the source ptr is not empty
          propagated |= (funcPtsGraph[dstNode].insert(itr->second) > 0);
        } else if (funcPts.find(I) != funcPts.end()) {
          // we are expecting point2 from the resulting ptr
          CG_LOG("Select: src node not found in the graph: " << srcNode << "\n");
          funcPts.insert(I->getOperand(i));
          Changed |= findDefinitions(I->getOperand(i), worklist);
        }
      }
      break;
    }
    default: {
      WARNING("Unhandled instruction: " << *I << "\n");
    }
    } // end switch

    if (propagated) {
      // add current node to the ptr set
      funcPts.insert(I);
      // add all users of I to the workset
      for (User *U : I->users()) {
        if (Instruction *UI = dyn_cast<Instruction>(U)) {
          worklist.push_back(UI);
        }
      }
    }
  }

  return Changed;
}

void CallGraphPass::collectUsers(Value *V) {
  if (funcPts.insert(V).second == false)
    return;
  for (User *U : V->users()) {
    if (Instruction *I = dyn_cast<Instruction>(U)) {
      _workset.insert(I);
    } else if (Constant *C = dyn_cast<Constant>(U)) {
      for (User *CU : C->users()) {
        collectUsers(CU);
      }
    } else {
      WARNING("Unhandled user type: " << *U << "\n");
    }
  }
}

bool CallGraphPass::doInitialization(Module *M) {

  for (Function &F : *M) {
    // initialize callers
    auto RF = getFuncDef(&F);
    CallInstSet &CIS = Ctx->Callers[RF]; // use RF to retrieve callers
    for (User *U : F.users()) {
      if (CallInst *CI = dyn_cast<CallInst>(U)) {
        if (CI->getCalledFunction() == &F)
          CIS.insert(CI);
      }
    }

    // collect address-taken functions
    if (F.hasAddressTaken()) {
      collectUsers(&F);
      Ctx->AddressTakenFuncs.insert(&F);

      // only add fval -> fobj edge in call graph analysis?
      NodeIndex valNode = NF.createValueNode(&F);
      NodeIndex objNode = AndersNodeFactory::InvalidIndex;
      if (Ctx->ExtFuncs.find(F.getName().str()) != Ctx->ExtFuncs.end()) {
        // external function, no object node, create one
        objNode = NF.createObjectNode(&F);
      } else {
        // defined function, get the definition
        objNode = NF.getObjectNodeFor(&F);
      }
      assert(objNode != AndersNodeFactory::InvalidIndex && "Object node not found!");
      funcPtsGraph[valNode].insert(objNode);
      CG_LOG("AddressTaken: " << F.getName() << " : " << valNode << " -> " << objNode << "\n");
    }
  }

  return false;
}

bool CallGraphPass::doFinalization(Module *M) {

  // update callee mapping
  for (Function &F : *M) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      // map callsite to possible callees
      if (CallInst *CI = dyn_cast<CallInst>(&*i)) {
        FuncSet &FS = Ctx->Callees[CI];
        // calculate the caller info here
        for (const Function *CF : FS) {
          CallInstSet &CIS = Ctx->Callers[CF];
          CIS.insert(CI);
        }
      }
    }
  }

  return false;
}

bool CallGraphPass::doModulePass(Module *M) {
  bool Changed = true, ret = false;
  NF.setModule(M);
  NF.setDataLayout(&M->getDataLayout());
  while (Changed) {
    Changed = false;
    for (Function &F : *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
      Changed |= runOnFunction(&F);
    }
    ret |= Changed;
  }
  return ret;
}

// debug
void CallGraphPass::dumpFuncPtrs(raw_ostream &OS) {
  for (FuncPtrMap::iterator i = Ctx->FuncPtrs.begin(),
       e = Ctx->FuncPtrs.end(); i != e; ++i) {
    if (i->second.empty())
      continue;
    OS << i->first << "\n";
    FuncSet &v = i->second;
    for (FuncSet::iterator j = v.begin(), ej = v.end();
         j != ej; ++j) {
      OS << "  " << ((*j)->hasInternalLinkage() ? "f" : "F")
         << " " << (*j)->getName().str() << "\n";
    }
  }
}

void CallGraphPass::dumpCallees() {
    RES_REPORT("\n[dumpCallees]\n");
    raw_ostream &OS = outs();
    OS << "Num of Callees: " << Ctx->Callees.size() << "\n";
    for (CalleeMap::iterator i = Ctx->Callees.begin(), 
         e = Ctx->Callees.end(); i != e; ++i) {

        CallInst *CI = i->first;
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

void CallGraphPass::dumpCallers() {
    RES_REPORT("\n[dumpCallers]\n");
    for (auto M : Ctx->Callers) {
        const Function *F = M.first;
        CallInstSet &CIS = M.second;
        RES_REPORT("F : " << getScopeName(F) << "\n");

        for (auto *CI : CIS) {
            Function *CallerF = CI->getParent()->getParent();
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
