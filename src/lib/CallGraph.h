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
#include <tuple>
#include <vector>
#include <unordered_map>
#include <unordered_set>

#include "Global.h"
#include "ConstraintGraph.h"
#include "NamedCells.h"

// IR predicates the graph build and the baseline's export share.
bool shouldSkipValue(const llvm::Value *V); // compiler-introduced values
bool containsPointerType(llvm::Type *T);   // T is or holds a pointer
// A deterministic order on instructions for reports, where a pointer
// set's order follows the heap: function name, debug file:line, position
// in the function.
bool irOrderLess(const llvm::Instruction *A, const llvm::Instruction *B);
struct IROrder {
  bool operator()(const llvm::Instruction *A, const llvm::Instruction *B) const { return irOrderLess(A, B); }
};

// Builds the constraint graph from IR and resolves indirect calls with
// the rooted flows-to solver. The CFL-reachability baseline
// (src/baseline/CFLCGPass) derives from it to reuse the graph build and
// overrides the solve and the hooks marked "baseline".
class PointeeResolver;

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
  // --cfl-cells (PD): subs of two ptrtoints, whose result carries no facts.
  std::vector<const llvm::Instruction *> ptrDiffCuts;
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
    // Ruling A (plan 3.53, completes 1b): the element types of its scalar
    // accesses ("float", "i16", "i8"; a vector's element), the receiving
    // variable's declared scalar pointee, and whether the site accesses
    // it as pointers or structs, or passes it to a string function
    // (str*, sprintf: byte uses). memcpy/memmove/memset are neither.
    std::set<std::string> scalarTypes;
    std::string siteScalar;
    bool ptrAccess = false, structAccess = false, strUse = false;
    // The receiver is a struct field (row 3: 1b reads its declared member
    // type); the result's slot is a cursor walking the block (followed),
    // or a slot stored with other values too (the site unclassified).
    bool fieldReceiver = false, cursorSlot = false, slotUnclassified = false;
    // A struct-pointer field received it: a base-class slot, no declaration.
    bool structFieldSeen = false;
    // A3: struct evidence against a scalar label, never a label: (struct,
    // where) for a struct GEP on a join containing the result and for a
    // receiving field whose debug type points to a struct.
    std::vector<std::pair<std::string, std::string>> structAgainst;
    // A4: the structs the site's receiving variables or fields point to by
    // their debug type that the linked IR merged away under another name,
    // with their sizes in bytes; diSeen: some receiver has a debug type.
    std::map<std::string, uint64_t> mergedIdents;
    bool diSeen = false;
    // A5a: every struct the site's own receivers declare ("struct.N" by
    // debug name).
    std::set<std::string> declStructs;
    // A variable or field received it (declared or not): with no
    // declaration, its type declares nothing (char *, void *) by rule;
    // without one the result went straight to a return or a call.
    bool hasReceiver = false;
    // Reloads of a shared result slot that only the site's store reaches
    // (followed for segments only).
    size_t reachedReloads = 0;
    // Segments declared at the site (plan 3.53 rule 1, extent): a constant
    // offset c > 0 of the result cast to B* (the receiving variable's
    // declared pointee) or written through a B struct GEP; "" when two
    // declarations disagree.
    std::map<int64_t, std::string> segments;
    // A segment the site also indexes by a stride of its struct (`&aMem[i]`,
    // `pMem++` on VdbeFrameMem(pFrame)): an array of it without an extent
    // (the struct analogue of ruling A's scalar and 1b's pointer-slot
    // arrays). Offset -> struct; "" when two strides disagree.
    std::map<int64_t, std::string> segStrides;
    // Segment declarations read from a struct field receiving the address.
    size_t segFieldReceivers = 0;
  };
  void labelAllocationSites(
      std::unordered_map<const llvm::CallBase *, AllocSiteLabel> &siteLabel,
      size_t &allocCalls, size_t &wrapperCalls);
  void allocationsOfCall(const llvm::CallBase *C,
                         std::set<const llvm::CallBase *> &out);
  void staticLabels(
      std::unordered_map<const llvm::Value *, std::set<std::string>> &out);
  // Per allocation call: the segments its creating sites declare (several
  // creating sites: kept only where they agree).
  std::unordered_map<const llvm::Value *, std::map<int64_t, std::string>> allocSegments;
  // The offsets of those segments the site indexes as arrays of their struct.
  std::unordered_map<const llvm::Value *, std::set<int64_t>> allocSegmentArrays;
  // Allocations every creating site uses only as bytes (char accesses,
  // string functions): marked used as bytes at mint (ruling A; a mark,
  // not a label).
  std::unordered_set<const llvm::Value *> allocBytesOnly;
  // A3 (Fable 2026-10-21): allocations whose agreed scalar label (ruling A)
  // meets struct evidence on the same object (a struct GEP on a join
  // containing the result, or a receiving field declared a struct
  // pointer): left unlabeled, a conflict; one rule report row each, in IR
  // order.
  std::vector<std::string> scalarConflictRows;
  // A4 (Fable 2026-10-20): per allocation, the debug identity its creating
  // sites' receivers declare for a struct the linked IR merged away, and
  // its size; applied at mint to a struct label of the same size.
  std::unordered_map<const llvm::Value *, std::pair<std::string, uint64_t>> allocMergedIdent;
  // A4: allocations none of whose sites has a receiver with a debug type
  // (the IR name stays, counted), and the rows of those whose sites name
  // several identities (the IR name stays, reported), in IR order.
  std::unordered_set<const llvm::Value *> allocNoDI;
  // A5a: per allocation, the structs its creating sites' own receivers
  // declare.
  std::unordered_map<const llvm::Value *, std::set<std::string>> allocDeclStructs;
  std::vector<std::string> identConflictRows;
  // The site census's counts for the rule report (staticLabels): sites,
  // sites whose only receiver is a struct-pointer field (no declaration),
  // sites whose receiver kind is unclassified (a result slot also holding
  // another value).
  size_t censusSites = 0, censusStructFieldOnly = 0, censusUnclassified = 0, censusSharedDeclared = 0,
         censusUndeclared = 0, censusReachedReloads = 0, censusSegFieldSites = 0;
  std::array<size_t, 5> censusSegments{}; // struct, of them arrays, ptr[], scal[], bytes
  // --cfl-union-keys: the key names of each keyed union access, filled by
  // runUnionCensus's inference before graph build, applied by the
  // load/store visitors (plan 3.17).
  std::map<const llvm::Instruction *, std::vector<std::string>> unionKeyNames;
  // ... and the accesses of a keyed union whose key is unknown, with the
  // union's name prefix "struct.S+off".
  std::map<const llvm::Instruction *, std::string> unionUnknownOf;
  // ... and the member the union census types each store into a union by
  // ("" when it types none; reporting only).
  std::map<const llvm::Instruction *, std::string> unionWriteMember;
  // Every union field of a struct (debug info), by "struct.S" and byte
  // offset: its field name, size, and the union census's short verdict
  // (read by the containers' cursor check, plan 3.55 Q-d).
  struct UnionFieldNote { std::string field; int64_t size = 0; std::string census; };
  std::map<std::string, std::map<int64_t, UnionFieldNote>> unionFieldNotes;
  // The union census's UNCHECKED reads (keyed by their own member with no
  // settling check, the user's rule of 2026-10-07), with the key it gave
  // each: a tag pair that keys one replaces its keys (TaggedFields), net of
  // which the final count is printed; a closure that rests on one lists it
  // (the containers' cursor check).
  std::map<const llvm::Instruction *, std::string> uncheckedReads;
  // (C') Union stores typed by a constant address's debug type: the listed
  // assumption per store (rule report).
  std::vector<std::string> unionAddrTyped;
  // R2: union stores typed by a declared embedding (rule report).
  std::vector<std::string> unionEmbedTyped;
  // (C'') One-field union copies (Fable 2026-10-17): a store whose value is
  // a load of the same union field (struct, union offset, offset in it,
  // size) of another object, directly or through an -O0 spill local, is a
  // per-key copy (a byte copy of the field, byteCopies): each key at the
  // source goes to the destination with its member component and the
  // store's own tag keys (unionCopyTags; empty on a census-only slot: the
  // same key). The store makes no store edge. Rows for the rule report;
  // the -O3 shapes left as ordinary stores, counted.
  std::map<const llvm::Instruction *, const llvm::LoadInst *> unionCopyOf;   // store -> the load it copies
  std::map<const llvm::Instruction *, std::vector<std::string>> unionCopyTags; // store -> its tag keys
  std::vector<std::pair<const llvm::Instruction *, std::string>> unionCopyRows; // in IR order (irOrderLess)
  size_t unionCopyVector = 0, unionCopyPhi = 0;
  // Tag fields 3.51 widened (no admitted tag), by "struct.S": "S+off: why".
  std::map<std::string, std::vector<std::string>> widenedTagsOf;
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
  // Container storage closure (plan 3.55 obligation 1, report only):
  // --cfl-container-closure (Containers.cc).
  void checkContainerClosure();
  // Its per-field report (fed / closed / open with reason): a rule-report
  // section.
  std::vector<std::string> containerClosureReport;
  // The containers' obligations (fed / O1-O6 verdicts): a rule-report
  // section.
  std::vector<std::string> containerReport;
  // Verified containers' rows, applied per call site outside the body
  // (plan 3.55): the row of each function, and each container's body.
  struct RowApply { size_t cont; GlobalContext::ContainerRow row; };
  std::map<const llvm::Function *, RowApply> containerRowOf;
  std::vector<std::set<const llvm::Function *>> containerBodies;
  // A row's transfer at one call site: the owner pointer; the facts that
  // enter the owner's element cell (an insert's element) and the node the
  // cell flows to (the call's result); the cell's name.
  struct RowLink { NodeIndex owner, in, out; uint32_t name; };
  std::vector<RowLink> rowLinks;
  // The element mint (Fable 2026-10-13): at an insert site s whose element
  // is its result (or an inline insert: an owner-code call to a
  // constructor), RET is the object (O, s, elem) for each owner object O,
  // minted as owner facts arrive; it enters the owner's element cell, the
  // body's element values (storage visibility, the body's own writes), and
  // inherits the fields the body writes on its own element (C -> row).
  struct MintLink {
    NodeIndex owner, out;
    uint32_t name;          // the element cell's name (UINT32_MAX: none)
    const llvm::Value *site;
    size_t cont;
  };
  std::vector<MintLink> mintLinks;
  size_t inlineInserts = 0; // (d): owner-code constructor calls minted
  // Per verified container: the body's element values (constructor results
  // in the body), the byte offsets the body writes on an element, and the
  // constructors (code-field targets) with the argument that carries the
  // owner.
  std::vector<std::vector<const llvm::Value *>> containerElemSources;
  std::vector<std::vector<int64_t>> containerInherit;
  std::vector<std::map<const llvm::Function *, unsigned>> containerCtors;
  // Per verified container: each code-field feed as (the owner value at
  // the feeding site, the constructors fed there), and each constructor's
  // element structs, in IR order (one per allocation size it measures): a
  // row object per (owner, element struct of a constructor fed to it).
  std::vector<std::vector<std::pair<const llvm::Value *, std::set<const llvm::Function *>>>> containerOwnerCtors;
  std::vector<std::map<const llvm::Function *, std::vector<llvm::StructType *>>> containerCtorType;
  // Snapshot holders ((3''), Fable 2026-10-18): a fresh block holding saves
  // of one owner's handle array and elements (Containers.cc). With its
  // entsize premise proven, the solver makes the block two objects: the
  // handle image (the allocation's own, a repeating pointer) and the
  // element image (one struct elem, at offset 0 of every element-region
  // pointer), and the element copies whole-struct copies of elem.
  struct SnapshotHolder {
    const llvm::Instruction *alloc = nullptr;
    llvm::StructType *elem = nullptr;
    std::vector<const llvm::Value *> elemPtrs; // region starts and steps, in IR order
    std::set<const llvm::Instruction *> elemCopies;
  };
  std::vector<SnapshotHolder> snapshotHolders;
  // After the solve: the pure rows' indirect calls against the solver's
  // targets (Containers.cc).
  void checkContainerPremises(bool stopped);
  std::unordered_map<const llvm::Instruction *, std::string> poolCarves;
  std::unordered_map<const llvm::Instruction *, std::string> poolCarvePool; // a certified carve -> its pool
  // A refused pool's carve -> its pool, and every pool's verdict as
  // reported ("POOL fields ...; carves ...; rewinds n" or "REFUSED ..."):
  // what a premise resting on a pool names (Containers.cc).
  std::unordered_map<const llvm::Instruction *, std::string> poolRefusedCarvePool;
  std::map<std::string, std::string> poolVerdicts;
  // A carve's size (plan 3.53 row 1), by form: before-bump the bump n,
  // counter the decrement, minus-len the length, all n * scale bytes;
  // header the chunk call's size minus off. Neither n nor chunk: the
  // form's size operand is not one of those shapes (unknown).
  struct CarveSize {
    const llvm::Value *n = nullptr;
    uint64_t scale = 1;
    const llvm::CallBase *chunk = nullptr;
    int64_t off = 0;
    // A before-bump carve whose bump is n, and the constant zeroK on the
    // blocks dominated by the true edge of `n == 0` (A2' (1)): "n, zeroK
    // when n == 0". -1: none.
    int64_t zeroK = -1;
    // How the size was read (A2' counters): 'z' the zero case above, 'h' a
    // header carve c followed by the store H := c + n (the piece is n).
    char how = 0;
  };
  std::unordered_map<const llvm::Instruction *, CarveSize> poolCarveSizes;
  // A heap allocation's size as a term of its callee, and the label and
  // extent it is minted with (AllocExtents.h).
  struct SizeTerms;
  // Every allocation call's mint decision, computed once at iteration 0
  // before the container closure (buildMintTable); the mint checks its own
  // decision against it.
  struct MintTable;
  std::shared_ptr<MintTable> mintTable;
  void buildMintTable();
  // Site names (B, Fable 2026-10-21; SiteNames.cc): a fresh allocation
  // site whose mint label is L, named L for the covers when every write
  // found from it is checked against L ((i)) and its size conforms
  // ((iii)); built from the mint table, before the container closure and
  // before every solve.
  struct SiteName {
    llvm::Type *layout = nullptr; // L's layout
    std::string label;
    int64_t size = 0;             // sizeof(L)
    bool repeats = false;         // an array of L
    bool trailing = false;        // L's trailing array runs on (A1 / gap 2)
    llvm::Type *trailElem = nullptr;
    int64_t trailAt = 0;          // the trailing array's first byte
    // 'n' named, 'o' open, 'f' FAIL, 's' untyped by size.
    char verdict = 0;
    std::string why;      // the open or FAIL kind; the size, untyped by size
    std::string first;    // its first write, with its location
    std::string sizeKind; // (iii)
    std::set<const llvm::Instruction *> found; // every write found from the site
    std::map<std::string, size_t> kinds;       // write kind -> count
    size_t cycles = 0, constOverPtr = 0, dataOverPtr = 0, unkeyedUnion = 0, keyedUnion = 0;
    bool pastIsTrailingObject = false; // a 'u'/'h' one-then-unknown block: bytes past L are another object's
  };
  // A write found from a site: by its web ((i)) or at the solve ((c)).
  struct FoundWrite {
    const llvm::Instruction *I;
    int64_t off; // -1: a runtime offset
    uint64_t bytes;
    llvm::Type *VT;
    const llvm::Value *V;
    char kind; // 's' struct step, 'u' store, 'm' memset (V: its byte), 'c' copy, 'o' open, 'n' NOOP call, 'b' bodiless byte write
    int64_t sd; // the stride it repeats at, 0 none
    std::string cat, why, srcName;
    int64_t srcOff = 0;
  };
  // Its verdict against S (a 'u', 'm' or 'c' write): cls "" when
  // checked (kind: what checked it), else the open kind or "FAIL", with why.
  struct WriteVerdict {
    std::string cls, why;
    std::vector<std::string> kinds; // what checked it (a store at a stride: two)
    bool inUnion = false, constOverPtr = false, dataOverPtr = false;
    std::tuple<std::string, uint64_t, uint64_t> unionSlot;
  };
  WriteVerdict judgeFoundWrite(const SiteName &S, const FoundWrite &w, const llvm::DataLayout &DL);
  // (c): the write I found at the solve at byte off of S's L (-1: an
  // any-offset cell is never passed), as (i) would record it.
  FoundWrite solveWrite(const llvm::Instruction *I, int64_t off);
  std::shared_ptr<PointeeResolver> solvePointees; // solveWrite's copy sources
  // (c) (Fable 2026-10-22): a site a write found at the solve does not
  // check loses its name for every later build (labels are only removed);
  // its row. Kept across iterations.
  std::map<const llvm::CallBase *, std::string> siteBrokenAtSolve;
  // Every (c) row, one per (site, write), over all iterations, in the order
  // found (IR order per solve).
  std::vector<std::string> siteBreakRows;
  std::set<std::pair<const llvm::CallBase *, const llvm::Instruction *>> siteBreakSeen;
  // The sites a cover's B6 decision rested on (close or reach), at the
  // closure (iteration 0), with each decision: a name broken at the solve
  // under one of them is refused, since covers are decided once.
  std::map<const llvm::CallBase *, std::vector<std::string>> siteCoverUsed;
  // The rows and the summary of siteNames (log: one line per site).
  void siteNamesReport(bool logRows);
  std::unordered_map<const llvm::CallBase *, SiteName> siteNames;
  std::vector<const llvm::CallBase *> siteNameOrder; // IR order
  std::vector<std::string> siteNameRows;             // not named, IR order (rule report)
  std::string siteNameSummary;
  void buildSiteNames();
  // Packed partial arrays (Fable 2026-10-22, rule (a)): a global whose
  // debug type is an array of T and whose IR type is a literal struct (a
  // partially initialized array, an array of union-initialized elements)
  // is labeled T[n] when its premise holds: equal allocation sizes, and
  // every leaf of the literal starts, modulo sizeof(T), at a leaf of T
  // with the same pointer-ness (padding: zero or undef). TypeLabels.cc;
  // the cells read a global's layout through globalLayout.
  std::map<const llvm::GlobalVariable *, llvm::Type *> packedArrayLayout;
  std::vector<std::string> packedArrayRows;    // IR order: labeled, then not labeled (rule report)
  size_t packedArrayLabeled = 0, packedArrayRefused = 0;
  void labelPackedArrays();
  llvm::Type *globalLayout(const llvm::GlobalVariable *GV) const;
  // A write of `bytes` at byte `off` of S's L, of value V (type VT):
  // "" when its span is a run of whole fields of L with pointer-ness equal
  // per field (B5), else why not. A union slot is the union census's.
  struct SiteWriteNote {
    bool inUnion = false, constOverPtr = false, dataOverPtr = false;
    std::tuple<std::string, uint64_t, uint64_t> unionSlot;
  };
  std::string judgeSiteWrite(const SiteName &S, int64_t off, uint64_t bytes, llvm::Type *VT, const llvm::Value *V,
                             const llvm::DataLayout &DL, SiteWriteNote *note = nullptr);
  // Do bytes [off, off + len) of S's L hold bytes [koff, koff + klen) of a
  // struct named KS ("struct.T") anywhere in its layout (B6)?
  bool siteWriteHolds(const SiteName &S, int64_t off, int64_t len, llvm::StringRef KS, int64_t koff, int64_t klen,
                      const llvm::DataLayout &DL);
  // staticLabels without its log lines (the table's call; the solve's own
  // call logs them where they always were).
  bool labelsQuiet = false;
  std::unordered_set<const llvm::Instruction *> poolBookkeeping;
  // The certified pools' handle fields ("objalloc+0"), checked after the
  // solve: a write into one outside the forms is a rule row.
  std::set<std::string> poolHandleFields;
  // A handle field that is an array (a link field's free[] lists, P1 G1):
  // its bytes; every cell from its offset up to offset + bytes is one of it.
  std::map<std::string, int64_t> poolHandleFieldBytes;
  // (d) (P1, Fable 2026-10-23): a certified pool whose free space takes
  // bytes before the bump that hands them out: its chunk allocation calls,
  // the chunk header's bytes (the refill offset), and the sites; the solve
  // withdraws the pool if a pointer fact lands in a chunk's free space.
  std::map<std::string, std::set<const llvm::Instruction *>> poolChunkAllocs;
  std::map<std::string, int64_t> poolChunkHeader;
  std::map<std::string, std::vector<std::string>> poolPreBump;
  // Stores whose value is a certified pool's handle value (the bump,
  // rewinds, refills into handle fields, chunk list links): not modeled.
  std::unordered_set<const llvm::Instruction *> poolHandleStores;
  // Loads and stores of a certified pool's handle fields, by pool (the
  // pool's representative field): the certificate the confirmer reads.
  std::unordered_map<const llvm::Instruction *, std::string> poolFieldAccess;
  // S1 (Fable 2026-10-23): the premise "every access to a handle field is
  // seen" is checked at the solve. An access whose address facts reach a
  // certified pool's handle cell and that the carve rule did not judge
  // withdraws the pool for every later iteration (pool -> its row); its
  // carves and handle stores get their ordinary edges then. A decision
  // that rested on the certificate (the confirmer's exemptions, the
  // container closure's) is recorded per pool: a withdrawn pool with one
  // is refused, as a cover's name is (siteCoverUsed).
  std::map<std::string, std::string> poolWithdrawnAtSolve;
  std::vector<std::string> poolWithdrawRows; // rule report, in the order found
  std::map<std::string, std::vector<std::string>> poolCertUsed;
  std::map<std::string, std::string> poolOfField; // certified handle field -> its pool
  size_t poolWithdrawnApplied = 0;                // withdrawals already applied to the graph
  std::unordered_map<const llvm::Instruction *, std::string> poolBookkeepingPool;
  // The certified pool whose certificate judged I (a carve, bookkeeping, a
  // handle-field access), or "".
  std::string poolOfInst(const llvm::Instruction *I) const {
    if (auto it = poolCarvePool.find(I); it != poolCarvePool.end()) return it->second;
    if (auto it = poolBookkeepingPool.find(I); it != poolBookkeepingPool.end()) return it->second;
    if (auto it = poolFieldAccess.find(I); it != poolFieldAccess.end()) return it->second;
    return "";
  }
  // A decision before the solve that rested on the certificate judging I.
  // While poolCertDefer is set (the container closure, whose uses count
  // only for a container it verifies) the use waits in poolCertDeferred.
  // A summarized slot a certified carve reloads: its stored values, kept
  // from the build for a withdrawal (applyPoolWithdrawals).
  std::map<NodeIndex, std::vector<NodeIndex>> poolSlotStoreVals;
  bool poolCertDefer = false;
  std::vector<std::pair<std::string, std::string>> poolCertDeferred; // (pool, what)
  void notePoolCertUse(const llvm::Instruction *I, const std::string &what) {
    const std::string p = poolOfInst(I);
    if (p.empty()) return;
    if (poolCertDefer) {
      poolCertDeferred.push_back({p, what});
      return;
    }
    auto &v = poolCertUsed[p];
    if (std::find(v.begin(), v.end(), what) == v.end()) v.push_back(what);
  }
  void applyPoolWithdrawals();
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
  // Link words (plan 3.55 R1, LinkWords.cc): integer fields holding a
  // pointer with tag bits, classified by store and load shape (report only);
  // the fields that pass.
  void computeLinkWords();
  std::vector<std::string> linkWordReport;
  std::set<std::pair<std::string, int64_t>> linkWordFields;
  // Every candidate's verdict ("PASS", "PASS with N assumptions", "FAIL ...")
  // and its ASSUMPTION sites, by "struct.T+off" (read by the containers'
  // LINKWORD storage, plan 3.55 R3).
  std::map<std::string, std::pair<std::string, std::vector<std::string>>> linkWordVerdicts;
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
  // P3 (Fable 2026-10-17): per read of both schemes, the writes it excludes
  // by their member name (the write, tagged: a tag/member disagreement);
  // reads in IR order, so the log lists them the same in every build.
  std::map<const llvm::Instruction *, std::vector<std::pair<const llvm::Instruction *, bool>>, IROrder> p3Excluded;
  size_t p3Reads = 0;
  // Per (tag-keyed read, writer): the maps on the provenance chains of the
  // tags by which the read's tests admit the writer (empty label: the
  // writer's own tag; recorded with the rule report or --verbose=2), and
  // the rule-report rows of the tag/member disagreements they explain.
  std::map<std::pair<const llvm::Instruction *, const llvm::Instruction *>, std::set<std::string>> taggedAdmitVia;
  std::vector<std::string> taggedDisagreeRows;
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
  // An allocation site's own value node, by the class representative
  // AllocSites holds: an object's Value is its allocation site, never the
  // representative of its dedup class (a formal, a cast). Two sites in one
  // class are two objects.
  std::unordered_map<NodeIndex, std::vector<NodeIndex>> AllocSiteNodes;
  void addAllocSite(NodeIndex rep, NodeIndex own) {
    AllocSites.insert(rep);
    auto &v = AllocSiteNodes[rep];
    if (std::find(v.begin(), v.end(), own) == v.end()) v.push_back(own);
  }

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
