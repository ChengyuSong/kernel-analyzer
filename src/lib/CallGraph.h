#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>

#include <unordered_set>
#include <boost/unordered/unordered_flat_set.hpp>

#include "Global.h"

class CallGraphPass : public IterativeModulePass {
private:
  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  bool handleCall(const llvm::CallBase*, const llvm::Function*);
  bool isCompatibleType(llvm::Type *T1, llvm::Type *T2);
  bool isCompatible(const llvm::CallBase*, const llvm::Function*);
  bool findCalleesByType(const llvm::CallBase*, FuncSet&);
  void buildEdgesFromPtsGraph(const PtsGraph &ptsGraph);

  AndersNodeFactory &NF;
  StructAnalyzer &SA;
  CFLEdgeBuilder &EB;
  PtsGraph funcPtsGraph;

  unsigned iteration;

  using node_set_t = std::unordered_set<NodeIndex>;

  boost::unordered_flat_set<const llvm::Value*> funcPts; // values that may reach a fptr
  boost::unordered_flat_set<NodeIndex> funcPtsObj; // objects that may reach a fptr
  std::unordered_set<const llvm::Function*> reachable; // reachable from main
  std::unordered_set<const llvm::Function*> unvisited; // visited functions
  node_set_t unresolvedFPts; // fptrs that are not resolved

  std::unordered_map<const StructInfo*, node_set_t> retStructs; // structs returned by functions
  std::unordered_map<const StructInfo*, node_set_t> argStructs; // structs passed as arguments
  std::unordered_map<const StructInfo*, node_set_t> globalStructs; // structs stored in globals

  CalleeMap calleeByType;

public:
  CallGraphPass(GlobalContext *Ctx_)
      : IterativeModulePass(Ctx_, "CallGraph"),
        NF(Ctx->nodeFactory), SA(Ctx->structAnalyzer), EB(Ctx->edgeBuilder),
        funcPtsGraph(Ctx->GlobalInitPtsGraph), // copy the init graph
        iteration(0)
        { }
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // debug
  void dumpFuncPtrs(llvm::raw_ostream &OS);
  void dumpCallees(llvm::raw_ostream &OS);
  void dumpCallers(llvm::raw_ostream &OS);
};

#endif
