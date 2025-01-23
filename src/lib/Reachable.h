#ifndef _REACHABLE_CALL_GRAPH_H
#define _REACHABLE_CALL_GRAPH_H

#include <llvm/IR/Value.h>

#include <deque>
#include <limits>
#include <unordered_set>
#include <unordered_map>

#include "Global.h"

class ReachableCallGraphPass {
private:
  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  bool isCompatibleType(llvm::Type *T1, llvm::Type *T2);
  bool findCalleesByType(llvm::CallInst*, FuncSet&);
  std::string getSourceLocation(const llvm::BasicBlock *BB);

  GlobalContext *Ctx;

  CalleeMap calleeByType;
  CallerMap callerByType;

  const bool UseTypeBasedCallGraph;

  std::vector<std::pair<std::string, int> > targetList;
  std::vector<std::string> entryList;
  std::unordered_set<const llvm::BasicBlock*> reachableBBs;
  std::unordered_map<const llvm::BasicBlock*, double> distances;
  std::unordered_set<const llvm::BasicBlock*> exitBBs;
  std::unordered_set<const llvm::BasicBlock*> entryBBs;
  std::unordered_set<const llvm::CallBase*> reachableIndirectCalls;

public:
    ReachableCallGraphPass(GlobalContext *Ctx_, std::string &TargetList,
        std::string &EntryList, bool typeBased = true);
    virtual bool doInitialization(llvm::Module *);
    virtual bool doFinalization(llvm::Module *);
    virtual void run(ModuleList &modules);

    // simple bfs pass
    void collectReachable(std::deque<const BasicBlock*> &worklist,
        std::unordered_set<const BasicBlock*> &reachable);

    // debug
    void dumpDistance(std::ostream &OS, bool dumpSolution = false, bool dumpUnreachable = false);
    void dumpPolicy(std::ostream &OS);
    void dumpCallees();
    void dumpCallers();
};

#endif
