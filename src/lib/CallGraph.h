#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/GlobalIFunc.h>

#include <memory>
#include <cstdint>
#include <map>
#include <functional>
#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "Global.h"
#include "CompressedGraph.h"
#include "gracfl/include/utils/Reachability.hpp"
#include "gracfl/include/solvers/SolverFWGramParallel.hpp"

class CallGraphPass : public IterativeModulePass {
private:
  class InstHandler : public llvm::InstVisitor<InstHandler> {
  private:
    CallGraphPass &CGP;
    llvm::Function *F;
    unsigned icallCounter = 0;

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
    void visitExtractElementInst(llvm::ExtractElementInst &I);
    void visitInsertElementInst(llvm::InsertElementInst &I);
    void visitShuffleVectorInst(llvm::ShuffleVectorInst &I);
    void visitExtractValueInst(llvm::ExtractValueInst &I);
    void visitInsertValueInst(llvm::InsertValueInst &I);
    void visitIntToPtrInst(llvm::IntToPtrInst &I);
    void visitPtrToIntInst(llvm::PtrToIntInst &I);
    void visitBinaryOperator(llvm::BinaryOperator &I);
    void visitVAArgInst(llvm::VAArgInst &I);
    void visitFreezeInst(llvm::FreezeInst &I);
    void visitAddrSpaceCastInst(llvm::AddrSpaceCastInst &I);
    void visitAtomicRMWInst(llvm::AtomicRMWInst &I);
    void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &I);
    void visitMemTransferInst(llvm::MemTransferInst &I);
    void visitMemSetInst(llvm::MemSetInst &I);
    void visitInstruction(llvm::Instruction &I) {} // Default handler for unhandled instructions
  };

  friend class InstHandler;

  using cfl_result_t = gracfl::ReachabilityMatrix;
  // Field-store tracking for struct-field-aware indirect call filtering
  using FieldStoreKey = std::pair<std::string, unsigned>;
  struct FieldStoreKeyHash {
    size_t operator()(const FieldStoreKey &k) const {
      return std::hash<std::string>()(k.first) ^ (std::hash<unsigned>()(k.second) << 16);
    }
  };

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
                          int enclosingFieldIdx = -1,
                          NodeIndex addrNode = 0xffffffff /*InvalidIndex*/);

  // Field-sensitive CFL memory modeling (--cfl-field-buckets > 0).
  // Field pointers get matched f<bucket>/-f<bucket> edges instead of plain
  // assignment edges; unknown-offset accesses fall back to an assignment edge
  // plus a fx/-fx wildcard self-loop on the base (absorbs any field step).
  const llvm::DataLayout *curDL = nullptr;
  std::map<std::pair<NodeIndex, int64_t>, NodeIndex> fieldPtrNodes;
  std::unordered_set<NodeIndex> moduleFieldWildcardRoots;
  std::unordered_set<NodeIndex> moduleConstGEPFieldDone;
  int fieldBucket(int64_t off) const;
  NodeIndex getFieldPtrNode(NodeIndex parentCanon, int64_t off);
  bool decomposeGEPLevels(const llvm::GEPOperator *GEP,
                          const llvm::DataLayout &DL,
                          llvm::SmallVectorImpl<int64_t> &levels) const;
  void addFieldChainEdges(NodeIndex baseNode, NodeIndex resultNode,
                          llvm::ArrayRef<int64_t> levels);
  void applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode,
                          const char *why);
  void addFieldWildcardLoop(NodeIndex n, const char *why);
  std::map<std::string, size_t> wildcardReasons; // fallback category tally
  void ensureConstGEPFieldEdges(const llvm::ConstantExpr *CE);
  void sliceEdgesToFptrComponents(std::vector<size_t> &idx);
  bool runFlowsToResolution();
  std::unordered_set<NodeIndex> fptrSliceKept;
  void emitFieldwiseCopyEdges(NodeIndex srcAddr, NodeIndex dstAddr,
                              llvm::Type *Ty, unsigned depth);

  // Pre-solve copy/field merge (--cfl-presolve-merge): solve the memory-free
  // sublanguage (a/-a/f* edges only; M rules cannot fire without d edges),
  // then collapse mutual-V' classes into canonicalNodeMap before the full
  // solve, so the d/-d interaction runs on class representatives.
  void preSolveCopyFieldMerge(const std::vector<gracfl::Edge> &edges,
                              const std::vector<size_t> *idx);
  void mergeCanonicalClasses(NodeIndex a, NodeIndex b);

  static bool getGEPStructField(const llvm::GEPOperator *GEP,
                                 std::string &structName, unsigned &fieldIdx);
  bool getGlobalFieldBoundaryKey(const llvm::Value *V,
                                 std::string &key) const;
  bool getCallSiteFieldKey(const llvm::Value *FPtr,
                           std::string &structName,
                           unsigned &fieldIdx) const;
  bool getFieldKeyFromPointerOperand(const llvm::Value *Ptr,
                                     std::string &structName,
                                     unsigned &fieldIdx,
                                     llvm::Type *&fieldTy) const;
  void buildFieldStoreMapFromIR(llvm::Module *M);
  bool addFieldAlias(const FieldStoreKey &A, const FieldStoreKey &B);
  bool fieldFilterAccepts(const llvm::Function *F,
                          const std::string &callSiteStruct,
                          unsigned callSiteFieldIdx) const;
  bool handleContainerCall(const llvm::CallBase *CS, const llvm::Function *CF);
  bool applySummaryAtoms(const llvm::CallBase *CS,
                         const GlobalContext::FuncSummary &S);
  // Keyed pair-channels (CHAINREG/CHAINCALL): registrations and
  // dispatch sites collected during edge construction, wired per key
  // (cross product) after the last module. Keys are chain-head
  // globals; non-constant sides fall back pooled.
  struct ChainRegRec {
    const llvm::GlobalValue *key;
    const llvm::GlobalVariable *blk;
    llvm::Function *fn;
    int selfFk;
    const llvm::CallBase *cs;
  };
  struct ChainDispatchRec {
    const llvm::CallBase *cs;
    const llvm::GlobalValue *key;
    llvm::SmallVector<std::pair<int, int>, 2> binds; // (fk, arg idx)
  };
  std::vector<ChainRegRec> chainRegs;
  std::vector<ChainDispatchRec> chainDispatches;
  bool chainFinalized = false;
  void finalizeChainPairs();
  const llvm::GlobalValue *canonChainKey(const llvm::GlobalValue *G);
  // Certified (ops-global, container) pairs (task #30): members from
  // the const initializer; containers from the complete use walk.
  struct OpsPairRec {
    FuncSet members;
    std::vector<const llvm::Value *> containers;
  };
  std::map<const llvm::GlobalVariable *, OpsPairRec> opsPairs;
  void certifyOpsPairs();
  void wireCallArgs(const llvm::CallBase *CS, const llvm::Function *CF);
  void confirmFreshWrappers();
  void runInvokeCensus();
  void runFieldChannelCensus();
  void confirmInvokeSummaries();
  void handleInlineAsm(llvm::CallBase &CS);
  bool findCustomAllocators(const cfl_result_t &outputCFLGraph,
                            bool rewriteEdges = true);
  bool findCustomAllocatorsComposed(
      const cfl_result_t &composedGraph,
      const std::unordered_map<std::string, uint32_t> &symbolToDense);
  bool lookupRetDense(const llvm::Function *F,
                      const std::unordered_map<std::string, uint32_t> &symMap,
                      uint32_t graphSize, uint32_t &retDense) const;
  bool lookupArgDense(const llvm::Function *F, unsigned argNo,
                      const std::unordered_map<std::string, uint32_t> &symMap,
                      uint32_t graphSize, uint32_t &argDense) const;
  bool lookupVarargDense(const llvm::Function *F,
                         const std::unordered_map<std::string, uint32_t> &symMap,
                         uint32_t graphSize, uint32_t &varargDense) const;
  bool handleIndirectCall(const cfl_result_t &outputCFLGraph,
                          const CallInstSet &indirectCalls);
  void collectLocalAllocaSummaries(const llvm::Function *F);
  bool isSummarizableAlloca(const llvm::AllocaInst *AI) const;
  bool resolveSummarizedAllocaSlot(const llvm::Value *Ptr, NodeIndex &slotRep);
  void emitLocalAllocaSummaryEdges();
  NodeIndex getRepNodeForValue(const llvm::Value *V);
  NodeIndex getCanonicalNode(NodeIndex n) const;
  void collectCanonicalMembers(NodeIndex n, std::vector<NodeIndex> &out) const;
  NodeIndex getRepDerefNode(NodeIndex ptrNode);
  void addAssignmentEdge(NodeIndex src, NodeIndex dst);

  // Global union-find dedup
  std::vector<NodeIndex> globalUFParent;
  std::vector<uint8_t> globalUFRank;
  void runGlobalDedup();
  bool globalDedupScanFunction(const llvm::Function *F);
  bool globalDedupScanAccessPaths();
  void globalDedupScanCallEdges(const llvm::Function *F,
                                const llvm::DenseSet<const llvm::Function *> &singleCallsiteCallees);
  const llvm::Function *resolveDirectCallee(const llvm::CallBase *CS);
  NodeIndex globalFind(NodeIndex n);
  bool globalUnion(NodeIndex a, NodeIndex b);
  void globalDedupFinalize();

  // Dense ID mapping (after global dedup)
  std::vector<uint32_t> origToDense;
  std::vector<NodeIndex> denseToOrig;
  uint32_t numDenseNodes = 0;
  std::vector<gracfl::Edge> denseEdges;
  void buildDenseMapping();
  uint32_t getDenseID(NodeIndex origNode) const;

  // V-SCC computation and constraint graph compression
  void computeVSCC(const cfl_result_t &outputCFLGraph, unsigned labelV,
                   std::vector<uint32_t> &nodeToSCC, uint32_t &numSCCs);
  void compressConstraintGraph(const cfl_result_t &outputCFLGraph,
                               const std::vector<uint32_t> &nodeToSCC,
                               uint32_t numSCCs,
                               CompressedGraphData &out);

  // Per-TU compositional solving
  std::vector<CompressedGraphData> perTUGraphs;
  void solveAndCompressPerTU(llvm::Module *M, size_t edgeStart, size_t edgeEnd);
  std::unordered_map<llvm::Module *, std::pair<size_t, size_t>> moduleEdgeRanges;
  llvm::DenseMap<const llvm::Module *, CallInstSet> moduleIndirectCallInsts;

  // Compositional solve results (for V-snapshot export)
  std::unique_ptr<gracfl::SolverFWGramParallel> composedSolver;
  std::unordered_map<std::string, uint32_t> composedSymbolToDense;
  uint32_t composedNumDense = 0;

  AndersNodeFactory &NF;
  CFLEdgeBuilder &EB;
  unsigned cflThreads;
  std::unique_ptr<gracfl::SolverFWGramParallel> cflSolver;
  size_t cflSolvedInputEdgeCount;
  bool cflForceRebuild;
  std::unordered_map<NodeIndex, NodeIndex> canonicalNodeMap;
  std::unordered_map<NodeIndex, std::unordered_set<NodeIndex>> canonicalClassMembers;
  std::unordered_set<NodeIndex> localSummarizedAllocaSlots;
  std::unordered_map<NodeIndex, std::vector<NodeIndex>> localAllocaStoreVals;
  std::unordered_map<NodeIndex, std::vector<NodeIndex>> localAllocaLoadVals;
  std::unordered_set<NodeIndex> moduleDerefEdgeRoots;

  unsigned iteration;

  std::unordered_set<NodeIndex> AllocSites;

  CalleeMap calleeByType;

  // ifunc symbol -> resolved target functions
  llvm::DenseMap<const llvm::GlobalIFunc*, FuncSet> IFuncTargets;

  void collectIFuncTargets(const llvm::GlobalIFunc *IF);
  void processCtorsDtors(llvm::Module *M);

  // Linker-mediated pointer arrays (task #22): section name -> members
  // (IR globals carrying that section attribute + module-asm PREL32
  // entry targets). Consumed by wireLinkerSectionArrays(), which
  // aliases each undefined __start_X/__stop_X extern to its members so
  // loads through the bounds symbols stop resolving to nothing.
  // in-place members: IR globals carrying the section attribute — the
  // linker lays THEM OUT as the array elements, so the bounds symbol
  // aliases the member objects (value edges).
  std::map<std::string, std::set<const llvm::GlobalValue*>> linkerSectionInPlace;
  // encoded members: module-asm PREL32 entry targets — the array holds
  // offsets ENCODING them, so they live in deref(bounds), read out by
  // the offset_to_ptr pull rule in visitIntToPtrInst.
  std::map<std::string, std::set<const llvm::GlobalValue*>> linkerSectionEncoded;
  // wired sections with module-asm entries that LOOK like symbols but
  // resolve to nothing: membership may be incomplete, so the bounds
  // symbol keeps the universal fallback (no override, no wiring)
  std::map<std::string, size_t> linkerSectionUnresolved;
  bool linkerArraySources(llvm::StringRef boundsName,
                          std::set<const llvm::GlobalValue*> &inPlace,
                          std::set<const llvm::GlobalValue*> &encoded,
                          bool *unresolved);
  void wireLinkerSectionArrays();

  std::unordered_map<const llvm::Function*,
                     std::unordered_set<FieldStoreKey, FieldStoreKeyHash>> funcFieldStores;
  // Soundness of the field filter requires per-function completeness: any
  // unclassified escape of a function's address disables filtering for it.
  std::unordered_set<const llvm::Function*> funcFieldStoresIncomplete;
  llvm::DenseSet<std::pair<const llvm::CallBase*, unsigned>> fieldTraceOK;
  // Set when any fixed-point loop stops at its iteration cap: the result may
  // under-approximate. Reported in the callgraph JSON.
  bool soundnessCapped = false;
  std::unordered_map<FieldStoreKey,
                     std::unordered_set<FieldStoreKey, FieldStoreKeyHash>,
                     FieldStoreKeyHash> fieldAliasMap;

public:
  CallGraphPass(GlobalContext *Ctx_);
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // debug
  void dumpFuncPtrs(llvm::raw_ostream &OS);
  void dumpGlobals(llvm::raw_ostream &OS);

  // export
  void dumpCallGraphJSON(llvm::StringRef Path);
  void dumpVSnapshot(llvm::StringRef Path);
  void dumpComposedVSnapshot(llvm::StringRef Path);
  void exportCompressedGraph(llvm::StringRef Path);
  bool runCompositionalSolve();
};

#endif
