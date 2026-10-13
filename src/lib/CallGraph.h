#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include <llvm/IR/Value.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/GlobalIFunc.h>

#include <memory>
#include <cstdint>
#include <map>
#include <set>
#include <functional>
#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "Global.h"
#include "ConstraintGraph.h"
#include "NamedCells.h"

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
    void visitVAStartInst(llvm::VAStartInst &I);
    void visitVACopyInst(llvm::VACopyInst &I);
    void visitFreezeInst(llvm::FreezeInst &I);
    void visitAddrSpaceCastInst(llvm::AddrSpaceCastInst &I);
    void visitAtomicRMWInst(llvm::AtomicRMWInst &I);
    void visitAtomicCmpXchgInst(llvm::AtomicCmpXchgInst &I);
    void visitMemTransferInst(llvm::MemTransferInst &I);
    void visitMemSetInst(llvm::MemSetInst &I);
    void visitInstruction(llvm::Instruction &I) {} // Default handler for unhandled instructions
    // A certified pool's carve is its own allocation site; any other
    // instruction goes to its handler.
    using llvm::InstVisitor<InstHandler>::visit;
    void visit(llvm::Instruction &I);
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
  // A method call (*(p.path.slot))(.., p, ..): the method is loaded
  // through a path of constant field steps and loads from an argument p
  // (C: p->f(p), p->ops->f(p); C++: p->vptr[k](p)). Returns the argument
  // index of p (-1 if none). levels[i] = (the pointer stepped at level i,
  // the address loaded at level i): level 0 starts at p, the last level's
  // load is the callee.
  int dispatchReceiver(
      const llvm::CallBase *CS,
      std::vector<std::pair<const llvm::Value *, const llvm::Value *>> *levels = nullptr);
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
  // extent: a strided step's covered length; an arith (constant index)
  // step's element size.
  // written: a typed or strided step of an unoptimized (optnone) function,
  // whose types are the program's own: its address into an array is the
  // array's (plan 3.43 provenance). -O3 may rebase a field on a
  // neighbouring one (inbounds bounds only the allocation).
  // writes: the step's address is written through (a store's address or a
  // memcpy/memmove destination, through further GEPs and casts); only
  // such a step labels an unlabeled object (plan 3.53, rule 1).
  // elem: the element struct a strided or constant-index level steps over
  // (T in `gep T, p, i`): typed evidence that an object is an array of T.
  struct LazyLabel { int64_t off; uint32_t stride; bool arith; const llvm::StructType *ty; uint32_t extent; bool written = false; bool writes = false; const llvm::StructType *elem = nullptr; };
  std::vector<LazyLabel> lazyLabels;
  std::map<std::tuple<int64_t, uint32_t, bool, const llvm::StructType *, uint32_t, bool, bool, const llvm::StructType *>, uint32_t> lazyLabelIdx;
  bool gepWritten = false; // the GEP being built is in an optnone function
  bool gepWrites = false;  // the GEP being built is written through
  // The element struct of each level of the GEP being built, and of the
  // level whose label is being made.
  llvm::SmallVector<const llvm::StructType *, 4> gepElems;
  const llvm::StructType *gepElem = nullptr;
  std::vector<std::tuple<NodeIndex, NodeIndex, uint32_t>> lazyFEdges; // src, dst, label
  // --cfl-cells: byte copies (memcpy, CPY summaries) as copy constraints
  // the cell solver resolves per cell pair: src, dst, length (-1 unknown).
  std::vector<std::tuple<NodeIndex, NodeIndex, int64_t, const llvm::Instruction *>>
      byteCopies; // (src, dst, length or -1, the copying call)
  // --cfl-cells: pointer subtractions (p, q, the sub): C defines p - q only
  // within one object; the solver reports pairs that are not.
  std::vector<std::tuple<NodeIndex, NodeIndex, const llvm::Instruction *>> ptrDiffs;
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
                          llvm::SmallVectorImpl<const llvm::StructType *> *types = nullptr,
                          llvm::SmallVectorImpl<const llvm::StructType *> *elems = nullptr) const;
  void addFieldChainEdges(NodeIndex baseNode, NodeIndex resultNode,
                          llvm::ArrayRef<int64_t> levels,
                          llvm::ArrayRef<const llvm::StructType *> types = {});
  void applyFieldFallback(NodeIndex baseNode, NodeIndex resultNode,
                          const char *why);
  void addFieldWildcardLoop(NodeIndex n, const char *why);
  std::map<std::string, size_t> wildcardReasons; // fallback category tally
  std::map<NodeIndex, std::string> wildcardWhy;   // per node (cells cycle report)
  // Integer names (plan 3.50 ruling): a struct field every access of
  // which, program-wide, is integer-typed, and no load of which reaches an
  // inttoptr. Loads from it carry no facts under --cfl-cells.
  std::map<std::pair<std::string, int64_t>, uint8_t> intNameFlags; // 1 ptr, 2 inttoptr, 4 non-int
  bool intNamesBuilt = false;
  void buildIntegerNames();
  bool isIntegerName(const llvm::Instruction *I, const llvm::Value *Addr, bool &counter);
  void ensureConstGEPFieldEdges(const llvm::ConstantExpr *CE);
  bool runFlowsToResolution();
  // --cfl-cells (CellSolver.cc, plan 3.26): inclusion over (object,
  // name) cells, no dereference-node unification.
  bool runCellResolution();
  bool wireResolvedCallee(const llvm::CallBase *CS, const llvm::Function *F);
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
                         bool *retBound = nullptr,
                         const llvm::Function *SF = nullptr);
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
  void wireCallArgs(const llvm::CallBase *CS, const llvm::Function *CF,
                    int skipArg = -1);
  void confirmFreshWrappers();
  void runInvokeCensus();
  void runConstructCensus();
  void runRegFieldGapReport(); // targeted-fs detector (post-solve)
  void confirmInvokeSummaries();
  void runSinkConfirmer(); // task #32: trace-payload read-back contract
  void runNexusCensus();      // task #38: nexus-struct discovery
  void runUnionCensus();      // --cfl-census-unions (UnionCensus.cc)
  // TypeLabels.cc: allocation calls labeled by their typed writes (IR
  // only), the allocations a call creates, and labels by value before
  // the solve (--cfl-weld-watch).
  struct AllocSiteLabel {
    std::set<std::string> types; // outermost struct of typed writes at offset 0
    std::string declared;        // the struct its debug-info variable declares
    std::string siteDeclared;    // the struct the receiving variable points to (debug info)
    std::string sitePtrArray;    // T** receiver: an array of pointer slots ("alent *")
    bool scalarUse = false;      // accessed as scalars/arrays (a buffer)
  };
  void labelAllocationSites(
      std::unordered_map<const llvm::CallBase *, AllocSiteLabel> &siteLabel,
      size_t &allocCalls, size_t &wrapperCalls);
  void allocationsOfCall(const llvm::CallBase *C,
                         std::set<const llvm::CallBase *> &out);
  void staticLabels(
      std::unordered_map<const llvm::Value *, std::set<std::string>> &out);
  // --cfl-union-keys: the key names of each keyed union access, filled by
  // runUnionCensus's inference before graph build, applied by the
  // load/store visitors (plan 3.17).
  std::map<const llvm::Instruction *, std::vector<std::string>> unionKeyNames;
  // ... and the accesses of a keyed union whose key is unknown, with the
  // union's name prefix "struct.S+off".
  std::map<const llvm::Instruction *, std::string> unionUnknownOf;
  // --cfl-union-keys=tag (cell solver): the keyed union slots (struct,
  // byte offset, size), and the dereference node of each keyed access with
  // its key (an interned cell name).
  std::set<std::tuple<std::string, uint64_t, uint64_t>> cellUnionSlots;
  boost::unordered_flat_map<NodeIndex, uint32_t> cellHubKey;
  std::map<std::pair<NodeIndex, uint32_t>, NodeIndex> keyedDerefOf;
  NodeIndex keyedDeref(NodeIndex ptr, const std::string &key);
  // --cfl-name-by-target: untyped writes whose unnamed-plane edge waits for
  // the solve to show a target other than a pointer variable:
  // (value, cell, the cell's unnamed shadow).
  std::vector<std::tuple<NodeIndex, NodeIndex, NodeIndex>> deferredUnnamed;
  bool isPointerVariable(const llvm::Value *V);
  // --cfl-census-names: unnamed pointer loads and stores (cell, is store).
  std::vector<std::pair<NodeIndex, bool>> unnamedAccessLog;
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

  // ---- Named cells (--cfl-named-planes; docs/named-cells-design.md) ----
  // A cell is the target of a Deref edge. Its shadow for name id n is a
  // cell reached by the same pointer that holds only the content filed
  // under n; AccessNames::Unnamed is the shadow of writes with no name.
  bool namedPlanes() const;
  NodeIndex namedShadow(NodeIndex cell, uint32_t name);
  // The pointer whose Deref edge reaches `cell`; InvalidIndex if none.
  NodeIndex cellParent(NodeIndex cell);
  bool isShadowCell(NodeIndex n) const { return shadowInfo.count(n) != 0; }
  // (cell, name) of a shadow; name 0 (Original) for any other node.
  std::pair<NodeIndex, uint32_t> shadowInfoOf(NodeIndex n) const;
  // A Deref target that is not a shadow.
  bool isCellNode(NodeIndex n);
  // A write from raw `src` (canonical `s`) into raw node `dst` that is
  // not filed by name: when dst is a cell, also write dst's unnamed
  // shadow; a copy from another cell relays shadows name by name.
  void fileUnnamedWrite(NodeIndex s, NodeIndex src, NodeIndex dst);
  // A load of value node `val` from `cell`: through name `name` it reads
  // the cell's shadows for that name and for unnamed writes; with no
  // name it reads the cell.
  void wireNamedLoad(NodeIndex cell, NodeIndex val,
                     llvm::ArrayRef<uint32_t> names);
  // A store of `val` into `cell` through name `name` (Unnamed: no name).
  void wireNamedStore(NodeIndex val, NodeIndex cell,
                      llvm::ArrayRef<uint32_t> names);
  void logNamedCells() const;
  // --cfl-census-type-labels (TypeLabels.cc): object labels from their
  // initializing writes, untyped writes retyped by them, named accesses
  // checked against them. Measurement only.
  void runTypeLabelCensus(
      const std::function<void(NodeIndex, std::vector<uint32_t> &)> &originsOf,
      const std::function<void(uint32_t, std::vector<const llvm::Value *> &)>
          &originValues,
      const std::function<bool(NodeIndex)> &anyFact,
      const std::function<std::string(NodeIndex, uint32_t, std::string &)>
          &explain,
      const std::string &emptyReadLine);
  std::vector<std::pair<NodeIndex, std::string>> blindWriteLog;
  std::vector<std::tuple<NodeIndex, uint32_t, const llvm::Instruction *>>
      namedAccessLog;
  // Before each solve: give pending writes of names now read their
  // shadows, and let the loads of names opened since the last solve read
  // the unnamed shadow.
  void ensureUnnamedShadows();
  // A write filed under `name`: into its shadow once some load reads the
  // name, pending until then.
  void fileNamedWrite(NodeIndex s, NodeIndex cell, uint32_t name);
  boost::unordered_flat_set<uint32_t> readNames;
  std::vector<std::tuple<NodeIndex, NodeIndex, uint32_t>> pendingNamedWrites;
  // Certificate (plan 3.7): a name is open once a typed write that names
  // no single leaf (variable offset, union, pun, several leaves, unknown
  // extent) may land on it; loads of names never opened skip the
  // unnamed shadow. Untyped writes (no struct position) open nothing
  // under --cfl-named-untyped=count and are counted (the blind spot).
  void openName(uint32_t name, llvm::StringRef culprit);
  void applyUnionKeys(const llvm::Instruction &I,
                      llvm::SmallVectorImpl<uint32_t> &names);
  void openStruct(llvm::StructType *S, llvm::StringRef culprit);
  // Struct position of the pointer through which a cell is written.
  ka::AccessNames::Position writerPosition(NodeIndex cell, std::string &where);
  bool namedCertifies() const;
  boost::unordered_flat_set<uint32_t> openNames;
  boost::unordered_flat_map<uint32_t, std::string> openWhy;
  uint64_t namedOpenEpoch = 0;
  // Named loads still reading only their name's shadow: (cell, value, name).
  std::vector<std::tuple<NodeIndex, NodeIndex, uint32_t>> certifiedReads;
  // Untyped writes into cells (the counted blind spot), by writer.
  uint64_t blindWrites = 0;
  std::map<std::string, uint64_t> blindBy;
  // Shape of the cell write being added: byte size of the value stored
  // (0: unknown), an offset from the cell's pointer the cell itself does
  // not carry (field-insensitive summary cells), and whether a write
  // from another cell moves one value rather than copying bytes in place
  // (a copy keeps names; a moved value is filed by its destination).
  uint64_t cellWriteSize = 0;
  int64_t cellWriteExtraOff = 0;
  bool cellWriteIsValue = false;
  struct CellWriteSize {
    CallGraphPass &P;
    uint64_t OldSz;
    int64_t OldOff;
    bool OldVal;
    CellWriteSize(CallGraphPass &P_, uint64_t Sz, int64_t ExtraOff = 0,
                  bool IsValue = false)
        : P(P_), OldSz(P_.cellWriteSize), OldOff(P_.cellWriteExtraOff),
          OldVal(P_.cellWriteIsValue) {
      P.cellWriteSize = Sz;
      P.cellWriteExtraOff = ExtraOff;
      P.cellWriteIsValue = IsValue;
    }
    ~CellWriteSize() {
      P.cellWriteSize = OldSz;
      P.cellWriteExtraOff = OldOff;
      P.cellWriteIsValue = OldVal;
    }
  };
  // Synthetic field pointers: node -> (base, byte offset).
  boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, int64_t>>
      fieldPtrOrigin;
  // Initializer slot: absolute byte offset in the global, and the global.
  uint64_t initAbsOff = 0;
  const llvm::GlobalVariable *initGV = nullptr;
  boost::unordered_flat_map<const llvm::GlobalVariable *, llvm::StructType *>
      initUseType;
  void initSlotWrite(NodeIndex val, NodeIndex cell);
  llvm::StructType *initUseTypeOf(const llvm::GlobalVariable *GV);
  uint64_t summaryWriteSize(int byteOff) const;
  // The named struct a function's formal points to (debug info, else the
  // one struct its body indexes it as); nullptr when unknown.
  llvm::StructType *formalStruct(const llvm::Function *F, unsigned ArgNo);
  boost::unordered_flat_map<uint64_t, llvm::StructType *> formalStructCache;
  // An explicit position for the cell write being added (summary atoms
  // write through a formal whose type the call site does not show).
  bool cellWriteHasPos = false;
  ka::AccessNames::Position cellWritePos;
  std::string cellWriteWhere;
  int64_t summaryCellOffset(int byteOff) const;
  std::unique_ptr<ka::AccessNames> accessNames;
  boost::unordered_flat_map<uint64_t, NodeIndex> shadowOf; // cell<<32|name
  boost::unordered_flat_map<NodeIndex, std::pair<NodeIndex, uint32_t>>
      shadowInfo;
  boost::unordered_flat_map<NodeIndex, NodeIndex> objCellParent;
  size_t objCellScan = 0;
  uint64_t objCellRemovals = 0;
  unsigned namedFiling = 0; // >0: the cell write being added is filed
  // Cell-to-cell copies (raw cells) and the names already relayed.
  std::vector<std::pair<NodeIndex, NodeIndex>> cellCopies;
  boost::unordered_flat_set<uint64_t> cellCopySeen;
  boost::unordered_flat_set<uint64_t> cellCopyNamed; // copy index<<32|name
  // Value node of each named load -> the cell it reads (measurement).
  boost::unordered_flat_map<NodeIndex, NodeIndex> namedLoadCells;
  struct NamedCellStats {
    uint64_t shadows = 0, namedStores = 0, unnamedStores = 0,
             namedLoads = 0, unnamedLoads = 0, namedSlots = 0,
             unnamedSlots = 0, unnamedWrites = 0, cellCopies = 0,
             typedWrites = 0, pointerVarWrites = 0;
  } namedStats;
  // processInitializer's slot position: innermost named struct and the
  // byte offset in it (array elements folded), or none / in a union.
  llvm::StructType *initNamedS = nullptr;
  uint64_t initOff = 0;
  bool initUnion = false;

  // Global union-find dedup
  std::vector<NodeIndex> globalUFParent;
  std::vector<uint8_t> globalUFRank;
  void runGlobalDedup();
  // Values global dedup must keep as their own nodes: the cell solver's
  // guard candidates (method-identity copies and reloads, method reloads
  // of a dispatch path from the receiver formal). A guard on a shared
  // node would filter every value of the class.
  std::unordered_set<const llvm::Value *> dedupKeep;
  void computeGuardCandidates();
  // Pool closure (plan 3.38): loads and stores of an allocator family's
  // pool fields that no other function touches; not modeled.
  std::unordered_set<const llvm::Instruction *> poolDrop;
  void checkPoolClosure();
  // Pool carves (plan 3.53 rule 3): forms, handle-field and chunk-base
  // checks, reported per pool (Carves.cc). With --cfl-pool-carves, the
  // carves of certified pools (each its own allocation site) and the
  // pools' own bookkeeping (handle-field stores, rewinds, pointer
  // arithmetic on handles: exempt from the confirmer's R3).
  void checkPoolCarves();
  std::unordered_map<const llvm::Instruction *, std::string> poolCarves;
  std::unordered_set<const llvm::Instruction *> poolBookkeeping;
  // The certified pools' handle fields ("objalloc+0"), checked after the
  // solve: a write into one outside the forms is a rule row.
  std::set<std::string> poolHandleFields;
  // Stores whose value is a certified pool's handle value (the bump,
  // rewinds, refills into handle fields, chunk list links): not modeled.
  std::unordered_set<const llvm::Instruction *> poolHandleStores;
  // Varargs renderers (plan 3.41): functions whose pointer reads through a
  // va_list are data only (printed, measured, compared, copied as chars):
  // those reads carry no facts; variadic wrappers whose va_lists reach only
  // such renderers get no call-site vararg wiring.
  std::unordered_set<const llvm::Function *> varargSinkRenderers, varargSinkWrappers;
  std::unordered_set<const llvm::Value *> varargSinkReads; // data-only va_arg reads
  void computeVarargSinks();
  // Varargs keyed by format specifier (plan 3.47): a printf-style list is
  // a tagged sequence whose tag is the specifier. The format parameter of
  // each function whose format reaches a mapped renderer; the keys a
  // renderer's va_arg read reads ("va#c": the specifiers whose cases
  // dominate it); all keys of the mapped renderers.
  std::map<const llvm::Function *, unsigned> varargFmtParam;
  std::map<const llvm::Value *, std::vector<std::string>> varargReadKeys;
  std::set<std::string> varargAllKeys;
  std::map<std::pair<const llvm::Function *, std::string>, NodeIndex> varargKeyNodes;
  NodeIndex varargKeyNode(const llvm::Function *F, const std::string &key);
  bool varargKeysAt(const llvm::CallBase *CS, const llvm::Function *CF,
                    std::vector<std::string> &keys);
  size_t varargKeyedSites = 0, varargPoolSites = 0, varargUnparsed = 0;
  size_t varargMapped = 0, varargKeyedReads = 0, varargUnkeyedReads = 0;
  std::vector<std::string> varargReport; // UNMAPPED / UNKEYED lines (rule report)
  void computeVarargKeys();
  // Tagged fields (plan 3.51): union keys for a pointer field tagged by a
  // sibling field of the same object (TaggedFields.cc).
  void computeTaggedFields();
  // Atom summaries adopted for bodies; withdrawn where keys apply.
  std::set<const llvm::Function *> adoptedAtomBodies;
  void unadoptKeyedBodies();
  std::vector<std::string> taggedReport;
  std::array<size_t, 11> taggedCounts{}; // ..., predicate tests closed, open, parameter-pair reads keyed, untested
  // Keyed tagged-field pairs (struct, F offset, D offset, D size): the solver
  // flips a pair to unkeyed when a byte copy writes its tag other than as a
  // co-move (plan 3.51, the in-solve certificate check).
  struct TaggedPair { std::string S; int64_t F, D, Dsize; };
  std::vector<TaggedPair> taggedPairs;
  // Stores whose pointer's provenance is not decidable locally (a
  // parameter, a loaded or returned pointer): the solver watches the root
  // value; a fact (S object, position covering a keyed tag) landing there
  // flips the pair (plan 3.51 ruling A/B). The store writes w bytes at
  // root + [lo, hi] (unb: anywhere in the object).
  struct TaggedWatch { const llvm::Value *root; int64_t lo, hi; bool unb; unsigned w; const llvm::Instruction *at; };
  std::vector<TaggedWatch> taggedWatches;
  // Alias assumptions (plan 3.51): the object `id` points to (its field at
  // offset `field`) is not one the accesses of access set `accSet` reach.
  // An access is a base pointer plus a constant offset (var: unknown).
  struct TaggedAccess { const llvm::Value *base; int64_t k; bool var; };
  struct TaggedAssume { const llvm::Value *id; int64_t field; uint32_t accSet; std::string site; };
  std::vector<std::vector<TaggedAccess>> taggedAccessSets;
  std::vector<TaggedAssume> taggedAssumes;
  // Entries whose function-pointer parameters were evaluated under the
  // outside-domain premise (plan 3.51 ruling a.2), with the parameter.
  std::map<const llvm::Function *, std::set<unsigned>> taggedOutsideEntries;
  // Functions whose address may reach the outside, pre-solve (the
  // evaluator's outside domain); the solver reports any it missed.
  std::set<const llvm::Function *> taggedOutsidePre;
  // Reads of a field with candidate tags that no tag test guards: they
  // admit every writer (field, site).
  std::vector<std::pair<std::string, const llvm::Instruction *>> taggedUntested;
  // Open retags no test guards (in-place retags without a content write):
  // (field and tag, site, map).
  std::vector<std::tuple<std::string, const llvm::Instruction *, std::string>> taggedInPlace;
  // Per-use parameter channels (plan 3.51, parameter-pair tests): a tested
  // use of a callee parameter reads, at each call site, the caller's load
  // of F through the keys its own test admits, instead of the parameter.
  std::map<const llvm::Instruction *, std::vector<std::pair<const llvm::Instruction *, std::vector<std::string>>>>
      taggedParamChannels;
  // The same uses: at a call that is not such a read, the call's content
  // argument when the use's tests can hold for the call's tag argument.
  std::map<const llvm::Instruction *, std::vector<const llvm::Value *>> taggedParamValueChannels;
  std::vector<std::vector<uint32_t>> taggedPairAssumes; // per taggedPairs entry
  // Method-installed state (plan 3.54): the dispatch o->D(o, ...) is a test
  // of D on o. A read of F through method M's receiver formal k is keyed
  // by D == M for the entries through such a dispatch (the formal's D
  // fields: struct, offsets; a method installed in several fields is
  // entered through any of them); the solver splits the formal's other
  // entries off, and they read F unkeyed.
  struct TaggedEntryFormal {
    const llvm::Function *M;
    unsigned k;
    std::string S;
    std::set<int64_t> Ds, Fs; // its test fields, the fields its entry-keyed reads read
  };
  std::vector<TaggedEntryFormal> taggedEntryFormals;
  std::map<const llvm::Instruction *, uint32_t> taggedEntryReads; // keyed read -> formal
  // The entry-keyed reads in IR order; a read's entry hub key is
  // "#entry<formal>.<index here>" (taggedEntryHubKey).
  std::vector<const llvm::Instruction *> taggedEntryReadList;
  std::map<const llvm::Instruction *, uint32_t> taggedEntryReadIdx;
  std::string taggedEntryHubKey(const llvm::Instruction *I) const {
    return "#entry" + std::to_string(taggedEntryReads.at(I)) + "." + std::to_string(taggedEntryReadIdx.at(I));
  }
  // Tag propagation along the receiver (plan 3.54 (b)): an object entering
  // a method X by a test carries the term {X}; passed on as an argument by
  // X (its receiver identity, F unwritten since X's entry), the callee's
  // formal receives X's terms for it. Per entry-keyed read, per D field,
  // per method X installed in D: the keys of the writers whose tag set
  // meets {X} ("*": every writer).
  std::map<const llvm::Instruction *, std::map<int64_t, std::map<const llvm::Function *, std::vector<std::string>>>>
      taggedEntryTermKeys;
  // The calls that pass a method formal's object on: (argument index, the
  // caller's formal), with the F fields unwritten from the caller's entry
  // to the call.
  struct TaggedChannel { unsigned k; uint32_t from; std::set<int64_t> Fs; };
  std::map<const llvm::CallBase *, std::vector<TaggedChannel>> taggedEntryChannels;
  // The dispatch sites that are tests: the callee loaded from D of the
  // receiver, nothing written between the load and the call.
  std::map<const llvm::CallBase *, std::pair<std::string, int64_t>> taggedEntrySites;
  // Entry-test refusals and counts for the rule report (plan 3.54 rows).
  std::vector<std::string> taggedEntryRows;
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
