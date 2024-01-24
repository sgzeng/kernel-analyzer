/*
 * Helper functions for point-to analysis
 *
 * Copyright (C) 2019 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>


#include <deque>

#include "Common.h"
#include "Annotation.h"
#include "PointTo.h"
#include "StructAnalyzer.h"

#define PT_LOG(stmt) KA_LOG(2, "Point2: " << stmt)

using namespace llvm;

static NodeIndex processStruct(const Value* v, const StructType* stType,
                               AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer) {

  if (stType->isOpaque()) {
    errs() << "Opaque struct type ";
    stType->print(errs());
    errs() << "\n";

    // we don't know how the struct looks like
    return nodeFactory.createObjectNode(v);
  }

  // Sanity check
  assert(stType != NULL && "structType is NULL");

  const StructInfo* stInfo = structAnalyzer.getStructInfo(stType, nodeFactory.getModule());
  assert(stInfo != NULL && "structInfoMap should have info for all structs!");

  // Empty struct has only one pointer that points to nothing
  if (stInfo->isEmpty())
    return nodeFactory.getNullObjectNode();

  // Non-empty structs: create one pointer and one target for each field
  unsigned stSize = stInfo->getExpandedSize();

  // We construct a target variable for each field
  // A better approach is to collect all constant GEP instructions and
  // construct variables only if they are used. We want to do the simplest thing first
  NodeIndex obj = nodeFactory.getObjectNodeFor(v);
  if (obj == AndersNodeFactory::InvalidIndex) { // avoid re-creating nodes
    obj = nodeFactory.createObjectNode(v, stInfo->isFieldUnion(0));
    for (unsigned i = 1; i < stSize; ++i)
      nodeFactory.createObjectNode(obj, i, stInfo->isFieldUnion(i));
  }

  return obj;
}

static NodeIndex createNodeForAggregateVal(const Value *v, const Type *type,
                                      AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer) {

  assert(valNode != AndersNodeFactory::InvalidIndex);

  // An array is considered a single variable of its type.
  while (const ArrayType *arrayType= dyn_cast<ArrayType>(type))
    type = arrayType->getElementType();

  // Now construct the memory object variable
  // It depends on whether the type of this variable is a struct or not
  NodeIndex obj = AndersNodeFactory::InvalidIndex;
  if (const StructType *structType = dyn_cast<StructType>(type)) {
    // check if the struct is a union
    if (!structType->isLiteral() && structType->getStructName().startswith("union"))
      obj = nodeFactory.createObjectNode(v, true);
    else
      obj = processStruct(v, structType, nodeFactory, structAnalyzer);
  } else {
    obj = nodeFactory.createObjectNode(v);
  }

  return obj;
}

static void createNodeForGlobals(Module *M, AndersNodeFactory &nodeFactory,
                                 StructAnalyzer &structAnalyzer, PtsGraph &ptsGraph) {

  for (auto const& GV: M->globals()) {
    if (GV.isDeclaration())
      continue;

    PT_LOG("Creating nodes for global " << GV.getName() << "\n");

    NodeIndex valNode = nodeFactory.createValueNode(&GV);

    const Constant *init = GV.getInitializer();
    if (init) {
      // defined global variables should have initializers
      NodeIndex objNode = AndersNodeFactory::InvalidIndex;
      if (isa<ConstantAggregate>(init)) {
        // well, since the GV is of (opaque) pointer type, we have to rely on the type of initializer
        const Type *type = init->getType();
        objNode = createNodeForAggregateVal(&GV, type, nodeFactory, structAnalyzer);
      } else {
        objNode = nodeFactory.createObjectNode(&GV);
      }
      ptsGraph[valNode].insert(objNode);
    } else {
      WARNING("GV:" << GV.getName() << ", no initializer\n");
    }
  }

  for (auto const& F: *M) {
    if (F.isDeclaration() || F.isIntrinsic() || F.empty())
      continue;

    PT_LOG("Creating nodes for function " << F.getName() << "\n");

    // Create return node
    Type *retType = F.getReturnType();
    if (!retType->isVoidTy()) {
      // handle aggregate return type
      if (retType->isArrayTy())
        createNodeForAggregateVal(&F, retType, nodeFactory, structAnalyzer);
      else if (retType->isStructTy())
        processStruct(&F, cast<StructType>(retType), nodeFactory, structAnalyzer);
      else
        nodeFactory.createReturnNode(&F);
    }

    // Create vararg node
    if (F.getFunctionType()->isVarArg())
      nodeFactory.createVarargNode(&F);

    // Add nodes for all formal arguments.
    for (auto const &A : F.args()) {
      // handle aggregate argument type
      if (A.getType()->isArrayTy())
        createNodeForAggregateVal(&A, A.getType(), nodeFactory, structAnalyzer);
      else if (A.getType()->isStructTy())
        processStruct(&A, cast<StructType>(A.getType()), nodeFactory, structAnalyzer);
      else
        nodeFactory.createValueNode(&A);
    }

    // Create node for address taken function
    if (F.hasAddressTaken()) {
      NodeIndex fVal = nodeFactory.createValueNode(&F);
      NodeIndex fObj = nodeFactory.createObjectNode(&F);
      ptsGraph[fVal].insert(fObj);
    }
  }
}

static void createNodeForHeapObject(const Instruction *I, int SizeArg, int FlagArg,
                                    AndersNodeFactory &nodeFactory, StructAnalyzer &structAnalyzer) {

  const PointerType* pType = dyn_cast<PointerType>(I->getType());
  assert(pType != NULL && "unhandled malloc function");

#if LLVM_VERSION_MAJOR > 13
  // Assuming opaque pointer type
  // We don't know what it points to, so we create an opaque object node
  nodeFactory.createOpaqueObjectNode(I, true);
  return;
#else
  const Type* elemType = pType->getElementType();

  // TODO: using casting is not the best way, consider sizeof
  if (elemType->isIntegerTy(8)) {
    // Check all the users of inst
    // TODO: use a working list to handle load/store
    for (auto U: I->users()) {
      if (const CastInst *CI = dyn_cast<CastInst>(U)) {
        pType = dyn_cast<PointerType>(CI->getType());
        if (!pType) continue;
        elemType = pType->getElementType();
        break;
      }
    }
  }

  unsigned maxSize = 0;
  uint64_t allocSize = 1;
  const StructInfo* stInfo = nullptr;
  bool isUnion = false;
  while (const ArrayType* arrayType = dyn_cast<ArrayType>(elemType)) {
    allocSize *= arrayType->getNumElements();
    elemType = arrayType->getElementType();
  }
  if (allocSize == 0) allocSize = 1;

  if (const StructType* structType = dyn_cast<StructType>(elemType)) {
    stInfo = structAnalyzer.getStructInfo(structType, nodeFactory.getModule());
    assert(stInfo != nullptr && "structInfoMap should have info for all structs!");
    if (!structType->isLiteral() && structType->getStructName().startswith("union"))
      isUnion = true;
    maxSize = stInfo->getExpandedSize();
    allocSize *= stInfo->getAllocSize();
  }

  // if size arg exists
  if (SizeArg >= 0) {
    const Value *SV = I->getOperand(SizeArg);
    if (const ConstantInt *size = dyn_cast<ConstantInt>(SV)) {
      uint64_t zext_size = size->getZExtValue();
      if (zext_size > allocSize) {
        assert(zext_size < (uint64_t)UINT_MAX);
        maxSize = zext_size;
      }
    }
  } else {
    // FIXME: kmem_cache_alloc
  }

  if (maxSize == 0) maxSize = StructInfo::getMaxStructSize();

  // Create the first heap node
  NodeIndex obj = nodeFactory.getObjectNodeFor(I);
  if (obj == AndersNodeFactory::InvalidIndex) {
    obj = nodeFactory.createObjectNode(I, isUnion, true);
    for (unsigned i = 1; i < maxSize; ++i) {
      isUnion = (stInfo && i < stInfo->getExpandedSize()) ? stInfo->isFieldUnion(i) : false;
      nodeFactory.createObjectNode(obj, i, isUnion, true);
    }
  }
#endif
}

void populateNodeFactory(GlobalContext &GlobalCtx) {

  AndersNodeFactory &nodeFactory = GlobalCtx.nodeFactory;
  StructAnalyzer &structAnalyzer = GlobalCtx.structAnalyzer;

  nodeFactory.setStructAnalyzer(&structAnalyzer);
  nodeFactory.setGobjMap(&GlobalCtx.Gobjs);
  nodeFactory.setFuncMap(&GlobalCtx.Funcs);

  PtsGraph &ptsGraph = GlobalCtx.GlobalInitPtsGraph;

  // universal ptr points to universal obj
  ptsGraph[nodeFactory.getUniversalPtrNode()].insert(nodeFactory.getUniversalObjNode());
  // universal obj points to universal obj
  ptsGraph[nodeFactory.getUniversalObjNode()].insert(nodeFactory.getUniversalObjNode());
  // null ptr points to null obj
  ptsGraph[nodeFactory.getNullPtrNode()].insert(nodeFactory.getNullObjectNode());
  // null obj points to nothing, so empty
  ptsGraph[nodeFactory.getNullObjectNode()];

  for (auto i = GlobalCtx.Modules.begin(), e = GlobalCtx.Modules.end(); i != e; ++i) {
    Module *M = i->first;
    nodeFactory.setDataLayout(&(M->getDataLayout()));
    nodeFactory.setModule(M);

    PT_LOG("Creating nodes for module " << M->getModuleIdentifier() << "\n");

    createNodeForGlobals(M, nodeFactory, structAnalyzer, ptsGraph);

    for (auto const& F: *M) {
      if (F.isDeclaration() || F.isIntrinsic() || F.empty())
        continue;
    
      int size, flag;
      if (isAllocFn(F.getName(), &size, &flag))
        continue;
    
      // Scan the function body
      // First, create a value node for each instruction
      for (auto itr = inst_begin(&F), ite = inst_end(&F); itr != ite; ++itr) {
        nodeFactory.createValueNode(&*itr);
      }

#if 0
      // Next, handle allocators
      for (auto itr = inst_begin(F), ite = inst_end(F); itr != ite; ++itr) {
        const Instruction *I = &*itr;
        switch (I->getOpcode()) {
          case Instruction::Alloca: {
            NodeIndex valNode = nodeFactory.getValueNodeFor(I);
            assert (valNode != AndersNodeFactory::InvalidIndex && "Failed to find alloca value node");
            assert (I->getType()->isPointerTy());
            createNodeForPointerVal(I, I->getType(), valNode, nodeFactory, structAnalyzer);
            break;
          }
          case Instruction::Call: {
            const CallInst *CI = dyn_cast<CallInst>(I);
            if (Function *CF = CI->getCalledFunction()) {
              if (isAllocFn(CF->getName(), &size, &flag)) {
                createNodeForHeapObject(CI, size, flag, nodeFactory, structAnalyzer);
              }
            }
            break;
          }
        }
      }
#endif
    }
  }
}

int64_t getGEPOffset(const Value* value, const DataLayout* dataLayout) {
  // Assume this function always receives GEP value
  //errs()<<"Inside getGEPOffset:\n";
  const GEPOperator* gepValue = dyn_cast<GEPOperator>(value);
  assert(gepValue != NULL && "getGEPOffset receives a non-gep value!");
  assert(dataLayout != nullptr && "getGEPOffset receives a NULL dataLayout!");

  int64_t offset = 0;
  const Value* baseValue = gepValue->getPointerOperand()->stripPointerCasts();
  // If we have yet another nested GEP const expr, accumulate its offset
  // The reason why we don't accumulate nested GEP instruction's offset is
  // that we aren't required to. Also, it is impossible to do that because
  // we are not sure if the indices of a GEP instruction contains all-consts or not.
  if (const ConstantExpr* cexp = dyn_cast<ConstantExpr>(baseValue))
    if (cexp->getOpcode() == Instruction::GetElementPtr) {
      offset += getGEPOffset(cexp, dataLayout);
    }
  Type* ptrTy = gepValue->getSourceElementType();
    
  SmallVector<Value*, 4> indexOps(gepValue->op_begin() + 1, gepValue->op_end());
  // Make sure all indices are constants
  for (unsigned i = 0, e = indexOps.size(); i != e; ++i) {
    if (!isa<ConstantInt>(indexOps[i]))
      indexOps[i] = ConstantInt::get(Type::getInt32Ty(ptrTy->getContext()), 0);
  }
  offset += dataLayout->getIndexedOffsetInType(ptrTy, indexOps);

  return offset;
}

unsigned offsetToFieldNum(const Value* ptr, int64_t offset, const DataLayout* dataLayout,
                          const StructAnalyzer *structAnalyzer, Module* module) {

  assert(ptr->getType()->isPointerTy() && "Passing a non-ptr to offsetToFieldNum!");
  assert(dataLayout != nullptr && "DataLayout is NULL when calling offsetToFieldNum!");
  if (offset < 0)
    return 0;

#if LLVM_VERSION_MAJOR > 13
  return 0;
#else
  Type* trueElemType = cast<PointerType>(ptr->getType())->getElementType();
  //errs()<<"Inside offset to field num:\n";
  //errs()<<"1trueElemType: "<<*trueElemType<<"\n";

  unsigned ret = 0;
  if (trueElemType->isStructTy()) {
    StructType* stType = cast<StructType>(trueElemType);
    if (!stType->isLiteral() && stType->getName().startswith("union"))
      return ret;
    if (!stType->isLiteral() && stType->getName().startswith("union"))
      return ret;
    if (stType->isOpaque())
      return ret;
  }

  while (offset > 0) {
    //errs()<<"offset: "<<offset<<"\n";
    // Collapse array type
    while(const ArrayType *arrayType= dyn_cast<ArrayType>(trueElemType))
      trueElemType = arrayType->getElementType();

    if (trueElemType->isStructTy()) {
      StructType* stType = cast<StructType>(trueElemType);

      const StructInfo* stInfo = structAnalyzer->getStructInfo(stType, module);
      assert(stInfo != NULL && "structInfoMap should have info for all structs!");
      stType = const_cast<StructType*>(stInfo->getRealType());

      const StructLayout* stLayout = stInfo->getDataLayout()->getStructLayout(stType);
      uint64_t allocSize = stInfo->getDataLayout()->getTypeAllocSize(stType);
      if (!allocSize)
        return 0;

      offset %= allocSize;
      unsigned idx = stLayout->getElementContainingOffset(offset);
      if (!stType->isLiteral() && stType->getName().startswith("union")) {
        offset -= stInfo->getDataLayout()->getTypeAllocSize(stType);
        if (offset <= 0)
          break;
      }
      ret += stInfo->getOffset(idx);

      if (!stType->isLiteral() && stType->getName().startswith("union")) {
        offset -= stInfo->getDataLayout()->getTypeAllocSize(stType);
      } else {
        offset -= stLayout->getElementOffset(idx);
      }
      trueElemType = stType->getElementType(idx);
    } else {
      //errs() << "trueElemType: " << *trueElemType<< "\n";
      offset %= dataLayout->getTypeAllocSize(trueElemType);
      if (offset != 0) {
        errs() << "Warning: GEP into the middle of a field. This usually occurs when union is used. Since partial alias is not supported, correctness is not guanranteed here.\n";
        break;
      }
    }
  }

  return ret;
#endif
}
