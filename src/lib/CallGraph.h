#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>
#include <llvm/IR/InstVisitor.h>

#include <unordered_set>

#include "Global.h"
#include "LLMClient.h"

class CallGraphPass : public IterativeModulePass {
private:
  class InstHandler : public llvm::InstVisitor<InstHandler> {
  private:
    CallGraphPass &CGP;
    llvm::Function *F;

  public:
    InstHandler(CallGraphPass &cgp, llvm::Function *func) : CGP(cgp), F(func) {}

    void visitReturnInst(llvm::ReturnInst &I);
    void visitCallBase(llvm::CallBase &CB);
    void visitAllocaInst(llvm::AllocaInst &I);
    void visitLoadInst(llvm::LoadInst &I);
    void visitStoreInst(llvm::StoreInst &I);
    void visitGetElementPtrInst(llvm::GetElementPtrInst &I);
    void visitBitCastInst(llvm::BitCastInst &I);
    void visitPHINode(llvm::PHINode &I);
    void visitSelectInst(llvm::SelectInst &I);
    void visitExtractValueInst(llvm::ExtractValueInst &I);
    void visitInsertValueInst(llvm::InsertValueInst &I);
    void visitIntToPtrInst(llvm::IntToPtrInst &I);
    void visitPtrToIntInst(llvm::PtrToIntInst &I);
    void visitVAArgInst(llvm::VAArgInst &I);
    void visitMemTransferInst(llvm::MemTransferInst &I);
    void visitMemSetInst(llvm::MemSetInst &I);
    void visitInstruction(llvm::Instruction &I) {} // Default handler for unhandled instructions
  };

  friend class InstHandler;

  using cfl_result_t = std::vector<std::vector<std::unordered_set<unsigned long long>>>;

  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  bool handleMemcpy(const llvm::CallBase*);
  bool handleCall(const llvm::CallBase*, const llvm::Function*);
  bool removeCallEdges(const llvm::CallBase*, const llvm::Function*);
  bool isCompatibleType(const llvm::Type *T1, const llvm::Type *T2);
  bool isStructLayoutCompatible(const llvm::StructType *ST1, const llvm::StructType *ST2);
  bool isCompatible(const llvm::CallBase*, const llvm::Function*);
  bool findCalleesByType(const llvm::CallBase*, FuncSet&);
  void processInitializer(NodeIndex obj, llvm::Constant *init);
  void queryAllocatorCandidatesWithLLM();
  bool findCustomAllocators(cfl_result_t &outputCFLGraph);
  bool handleIndirectCall(cfl_result_t &outputCFLGraph);

  AndersNodeFactory &NF;
  CFLEdgeBuilder &EB;
  LLMClient *LLM;

  unsigned iteration;

  std::unordered_set<NodeIndex> AllocSites;
  std::vector<llvm::Function*> PtrReturnFuncs;

  CalleeMap calleeByType;

public:
  CallGraphPass(GlobalContext *Ctx_, LLMClient *LLMClient_ = nullptr)
      : IterativeModulePass(Ctx_, "CallGraph"),
        NF(Ctx->nodeFactory), EB(Ctx->edgeBuilder), LLM(LLMClient_), iteration(0)
        { }
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // debug
  void dumpFuncPtrs(llvm::raw_ostream &OS);
  void dumpCallees(llvm::raw_ostream &OS);
  void dumpCallers(llvm::raw_ostream &OS);
  void dumpGlobals(llvm::raw_ostream &OS);
};

#endif
