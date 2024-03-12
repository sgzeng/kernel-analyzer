#ifndef _REACHABLE_CALL_GRAPH_H
#define _REACHABLE_CALL_GRAPH_H

#include <llvm/IR/Value.h>

#include <unordered_set>
#include <unordered_map>

#include "Global.h"

class ReachableCallGraphPass {
private:
  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  bool isCompatibleType(llvm::Type *T1, llvm::Type *T2);
  bool findCalleesByType(llvm::CallInst*, FuncSet&);

  GlobalContext *Ctx;

  CalleeMap calleeByType;
  CallerMap callerByType;

  std::vector<std::pair<std::string, int> > targetList;
  std::unordered_map<llvm::BasicBlock*, unsigned long> distances;
  std::unordered_set<llvm::BasicBlock*> exitBBs;

public:
    ReachableCallGraphPass(GlobalContext *Ctx_, std::string TargetList);
    virtual bool doInitialization(llvm::Module *);
    virtual bool doFinalization(llvm::Module *);
    virtual void run(ModuleList &modules);

    // debug
    void dumpDistance(llvm::raw_ostream &OS);
    void dumpCallees();
    void dumpCallers();
};

#endif
