#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>

#include <unordered_set>

#include "Global.h"

class CallGraphPass : public IterativeModulePass {
private:
  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
#if LLVM_VERSION_MAJOR > 10
  bool handleCall(llvm::CallBase*, const llvm::Function*);
#else
  bool handleCall(llvm::CallInst*, const llvm::Function*);
#endif
  bool isCompatibleType(llvm::Type *T1, llvm::Type *T2);
  bool findCalleesByType(llvm::CallInst*, FuncSet&);

  AndersNodeFactory &NF;
  StructAnalyzer &SA;
  PtsGraph funcPtsGraph;

  std::unordered_set<const llvm::Value*> funcPts; // values that may reach a fptr
  std::unordered_set<NodeIndex> funcPtsObj; // objects that may reach a fptr
  std::unordered_set<llvm::Function*> reachable; // reachable from main

  CalleeMap calleeByType;

public:
    CallGraphPass(GlobalContext *Ctx_)
        : IterativeModulePass(Ctx_, "CallGraph"),
          NF(Ctx->nodeFactory), SA(Ctx->structAnalyzer),
          funcPtsGraph(Ctx->GlobalInitPtsGraph) // copy the init graph
          { }
    virtual bool doInitialization(llvm::Module *);
    virtual bool doFinalization(llvm::Module *);
    virtual bool doModulePass(llvm::Module *);

    // debug
    void dumpFuncPtrs(llvm::raw_ostream &OS);
    void dumpCallees();
    void dumpCallers();
};

#endif
