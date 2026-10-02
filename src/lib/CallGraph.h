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
#include "ConstraintGraph.h"

// IR predicates the graph build and the baseline's export share.
bool shouldSkipValue(const llvm::Value *V); // compiler-introduced values
bool containsPointerType(llvm::Type *T);   // T is or holds a pointer

// Builds the constraint graph from IR and resolves indirect calls with
// the rooted flows-to solver. The CFL-reachability baseline
// (src/baseline/CFLCGPass) derives from it to reuse the graph build and
// overrides the solve and the hooks marked "baseline".
class CallGraphPass : public IterativeModulePass {
protected:
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

  // Field-store tracking for struct-field-aware indirect call filtering
  using FieldStoreKey = std::pair<std::string, unsigned>;
  struct FieldStoreKeyHash {
    size_t operator()(const FieldStoreKey &k) const {
      return std::hash<std::string>()(k.first) ^ (std::hash<unsigned>()(k.second) << 16);
    }
  };

  llvm::Function *getFuncDef(llvm::Function*);
  bool runOnFunction(llvm::Function*);
  // --cfl-reachable: process F's body (and, transitively, its direct and
  // summary-bound callees) the first time it is reached.
  void reachFunction(llvm::Function *F);
  void seedReachable();
  void reachLedger();
  bool handleMemcpy(const llvm::CallBase*);
  bool handleCall(const llvm::CallBase*, const llvm::Function*,
                  int opsSkipArg = -1);
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
  // Lazy addresses (--cfl-lazy-address, docs/lazy-address-design.md):
  // every f-edge carries an exact {offset, stride} label recorded out of
  // band (the grammar's residue labels are untouched). Index 0 is
  // reserved for offset 0 so "residue-0 f edge" keeps its meaning.
  // arith: the step came from element indexing or byte arithmetic (a
  // walk candidate), not from a struct member; only arithmetic offsets
  // take part in progression widening.
  // ty: the struct whose member this step selects (type witness for the
  // typed-heap conflict census); null for arithmetic / strided steps.
  // extent: byte length of the array a strided step indexes (0 = unbounded,
  // a pointer-level index or an unknown count). A variable index into
  // `[4 x ptr]` steps 8 bytes over 32; without the bound the strided
  // address overlapped every later slot of the object (bfd_target: 75 of
  // 107 slots read for `_bfd_check_format[fmt]`).
  struct LazyLabel { int64_t off; uint32_t stride; bool arith; const llvm::StructType *ty; uint32_t extent; };
  std::vector<LazyLabel> lazyLabels;
  std::map<std::tuple<int64_t, uint32_t, bool, const llvm::StructType *, uint32_t>, uint32_t> lazyLabelIdx;
  std::vector<std::tuple<NodeIndex, NodeIndex, uint32_t>> lazyFEdges; // src, dst, label
  uint32_t lazyLabelFor(int64_t off, uint32_t stride, bool arith = false,
                        const llvm::StructType *ty = nullptr, uint32_t extent = 0);
  void addFieldEdgesExact(NodeIndex src, NodeIndex dst, int64_t off,
                          uint32_t stride = 0, bool arith = false,
                          const llvm::StructType *ty = nullptr, uint32_t extent = 0);
  static constexpr int64_t kStridedLevelTag = (int64_t)1 << 62;
  static constexpr int64_t kArithLevelTag = (int64_t)1 << 61;
  NodeIndex getFieldPtrNode(NodeIndex parentCanon, int64_t off);
  bool decomposeGEPLevels(const llvm::GEPOperator *GEP,
                          const llvm::DataLayout &DL,
                          llvm::SmallVectorImpl<int64_t> &levels,
                          llvm::SmallVectorImpl<const llvm::StructType *> *types = nullptr) const;
  void addFieldChainEdges(NodeIndex baseNode, NodeIndex resultNode,
                          llvm::ArrayRef<int64_t> levels,
                          llvm::ArrayRef<const llvm::StructType *> types = {});
  void applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode,
                          const char *why);
  void addFieldWildcardLoop(NodeIndex n, const char *why);
  std::map<std::string, size_t> wildcardReasons; // fallback category tally
  void ensureConstGEPFieldEdges(const llvm::ConstantExpr *CE);
  bool runFlowsToResolution();
  // --cfl-dump-agraph: raw (pre-presolve) constraint graph + icall
  // site / function tables for offline reference solvers.
  void dumpRawGraph(const std::string &prefix);
  void runGTTypeCensus(const std::string &path);
  void dumpFnPtrOffsets();
  void emitFieldwiseCopyEdges(NodeIndex srcAddr, NodeIndex dstAddr,
                              llvm::Type *Ty, unsigned depth);

  // Pre-solve copy/field merge: quotient the memory-free sublanguage
  // (copy and field edges; no deref edges, so no M) by its V-components
  // (or, with --cfl-presolve-exact, its mutual-flow SCCs) into
  // canonicalNodeMap before the solve. idx: the edges of Graph to use
  // (all when null).
  void preSolveCopyFieldMerge(const std::vector<size_t> *idx);
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
  NodeIndex summaryDerefCell(NodeIndex base, int byteOff);
  NodeIndex summaryFieldPtr(NodeIndex base, int byteOff);
  NodeIndex summaryDeref2Cell(NodeIndex base, int byteOff);
  void runSummaryProvers(llvm::Module *M);
  bool applySummaryAtoms(const llvm::CallBase *CS,
                         const GlobalContext::FuncSummary &S,
                         bool *retBound = nullptr);
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
  void runStrataCensus(); // task #32 stratum-bridge census
  void wireCallArgs(const llvm::CallBase *CS, const llvm::Function *CF,
                    int skipArg = -1);
  void confirmFreshWrappers();
  void runInvokeCensus();
  void runFieldChannelCensus();
  void runCarveCensus(); // --cfl-census-carve: sub-allocation carving
  void runRegFieldGapReport(); // targeted-fs detector (post-solve)
  void confirmInvokeSummaries();
  void runSinkConfirmer(); // task #32: trace-payload read-back contract
  void runPtrToIntCensus(); // task #33: int-provenance residue sizing
  void runTracepointCensus(); // task #35: keyed-channel design sizing
  void runNexusCensus();      // task #38: nexus-struct discovery
  // task #35 keyed-channel model (--cfl-tracepoint-keys)
  std::pair<NodeIndex, NodeIndex>
  tracepointJunctions(const llvm::GlobalVariable *KeyGV);
  void bindTracepointProbe(const llvm::GlobalVariable *KeyGV,
                           const llvm::Value *ProbeV,
                           const llvm::Value *DataV, bool fromWalker);
  void bindTracepointMediatorPairs();
  void handleInlineAsm(llvm::CallBase &CS);
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

  // Indirect calls per module (the baseline's per-TU solve reads them).
  llvm::DenseMap<const llvm::Module *, CallInstSet> moduleIndirectCallInsts;

  AndersNodeFactory &NF;
  ConstraintGraph &Graph;
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
  // --cfl-const-channels: the cells a never-written (LLVM `constant`)
  // global's initializer stores into. The only legitimate writers of
  // constant memory; a store through a pointer that may point there is
  // impossible at run time and is not wired.
  std::unordered_set<NodeIndex> constInitCells;
  bool inConstInit = false;
  llvm::DenseSet<std::pair<const llvm::CallBase*, unsigned>> fieldTraceOK;
  // Set when any fixed-point loop stops at its iteration cap: the result may
  // under-approximate. Reported in the callgraph JSON.
  bool soundnessCapped = false;
  std::unordered_map<FieldStoreKey,
                     std::unordered_set<FieldStoreKey, FieldStoreKeyHash>,
                     FieldStoreKeyHash> fieldAliasMap;

  // Runs after the last module's graph build on every iteration;
  // returns true to request another iteration.
  virtual bool solve();
  void logHighDegreeNodes(size_t threshold, size_t topN);

  // Hooks (baseline): the flows-to binary never overrides them.
  // Called after each module's edges [edgeStart, edgeEnd) of Graph are
  // built, before linker arrays and chain pairs are wired.
  virtual void moduleBuilt(llvm::Module *, size_t edgeStart, size_t edgeEnd) {}
  // Graph-build choices that depend on the solver consuming the graph.
  virtual bool flowsTo() const { return true; }
  virtual bool compositional() const { return false; }
  virtual bool perTUSolve() const { return false; }
  virtual bool exportsCallBoundaries() const { return false; }

public:
  CallGraphPass(GlobalContext *Ctx_);
  virtual ~CallGraphPass() = default;
  virtual bool doInitialization(llvm::Module *);
  virtual bool doFinalization(llvm::Module *);
  virtual bool doModulePass(llvm::Module *);

  // export
  void dumpCallGraphJSON(llvm::StringRef Path);
};

#endif
