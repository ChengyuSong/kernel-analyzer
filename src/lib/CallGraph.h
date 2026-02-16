#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/GlobalIFunc.h>

#include <unordered_map>
#include <unordered_set>

#include "Global.h"
#include "gracfl/include/utils/Reachability.hpp"

class LLMClient;

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
    void visitBinaryOperator(llvm::BinaryOperator &I);
    void visitVAArgInst(llvm::VAArgInst &I);
    void visitMemTransferInst(llvm::MemTransferInst &I);
    void visitMemSetInst(llvm::MemSetInst &I);
    void visitInstruction(llvm::Instruction &I) {} // Default handler for unhandled instructions
  };

  friend class InstHandler;

  using cfl_result_t = gracfl::ReachabilityMatrix;

  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  bool handleMemcpy(const llvm::CallBase*);
  bool handleCall(const llvm::CallBase*, const llvm::Function*);
  bool removeCallEdges(const llvm::CallBase*, const llvm::Function*);
  bool isCompatibleType(const llvm::Type *T1, const llvm::Type *T2);
  bool isStructLayoutCompatible(const llvm::StructType *ST1, const llvm::StructType *ST2);
  bool isCompatible(const llvm::CallBase*, const llvm::Function*);
  bool findCalleesByType(const llvm::CallBase*, FuncSet&);
  void processInitializer(NodeIndex obj, llvm::Constant *init,
                          const std::string &enclosingStruct = "",
                          int enclosingFieldIdx = -1);

  static bool getGEPStructField(const llvm::GEPOperator *GEP,
                                 std::string &structName, unsigned &fieldIdx);
  void buildFieldStoreMap(const cfl_result_t &outputCFLGraph);
  bool handleContainerCall(const llvm::CallBase *CS, const llvm::Function *CF);
  bool findCustomAllocators(const cfl_result_t &outputCFLGraph);
  bool handleIndirectCall(const cfl_result_t &outputCFLGraph);

  AndersNodeFactory &NF;
  CFLEdgeBuilder &EB;
  LLMClient *LLM;
  unsigned cflThreads;

  unsigned iteration;

  std::unordered_set<NodeIndex> AllocSites;

  CalleeMap calleeByType;

  // ifunc symbol -> resolved target functions
  llvm::DenseMap<const llvm::GlobalIFunc*, FuncSet> IFuncTargets;

  void collectIFuncTargets(const llvm::GlobalIFunc *IF);
  void processCtorsDtors(llvm::Module *M);

  // Field-store tracking for struct-field-aware indirect call filtering
  struct FieldStoreRecord {
    NodeIndex valNode;
    std::string structName;  // stripped name (no LLVM suffix)
    unsigned fieldIdx;
  };
  std::vector<FieldStoreRecord> fieldStoreRecords;

  using FieldStoreKey = std::pair<std::string, unsigned>;
  struct FieldStoreKeyHash {
    size_t operator()(const FieldStoreKey &k) const {
      return std::hash<std::string>()(k.first) ^ (std::hash<unsigned>()(k.second) << 16);
    }
  };
  std::unordered_map<const llvm::Function*,
                     std::unordered_set<FieldStoreKey, FieldStoreKeyHash>> funcFieldStores;

public:
  CallGraphPass(GlobalContext *Ctx_, LLMClient *LLMClient_ = nullptr);
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // debug
  void dumpFuncPtrs(llvm::raw_ostream &OS);
  void dumpGlobals(llvm::raw_ostream &OS);

  // export
  void dumpCallGraphJSON(llvm::StringRef Path);
};

#endif
