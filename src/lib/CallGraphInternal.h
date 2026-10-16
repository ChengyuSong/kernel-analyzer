#ifndef KA_CALLGRAPH_INTERNAL_H
#define KA_CALLGRAPH_INTERNAL_H

// Declarations shared by the files that implement CallGraphPass
// (CallGraph.cc, GraphBuild.cc, Presolve.cc, FlowsToSolver.cc,
// Names.cc, Summaries.cc, Census.cc, Dump.cc). Not for other users.

#include <llvm/ADT/BitVector.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Module.h>
#include <functional>

#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/JSON.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SHA256.h>

#include <vector>
#include <array>
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <atomic>
#include <condition_variable>
#include <fstream>
#include <map>
#include <mutex>
#include <numeric>
#include <set>
#include <thread>
#include <unordered_map>
#include <unordered_set>

#include <cstdio>
#include <deque>
#include <sys/wait.h>
#include <unistd.h>

#include "CallGraph.h"
#include "BitPlane.h"
#include "IRCensus.h"
#include "Annotation.h"

#include "SCC.h"

#define CG_LOG(stmt) KA_LOG(2, "CallGraph: " << stmt)
#define CG_DEBUG(stmt) KA_LOG(3, "CallGraph: " << stmt)

using namespace llvm;


// --cfl-static-ops-tables (task #36): answer-level channel for
// static_call keys updated from ops-struct tables — the kvm_x86 /
// x86_pmu / apic_call families (1,225,715 pin pairs, ~all type-
// fallback: the update's fn argument is a dynamic load the graph
// never resolves). The update site's IR names the correlation
// structurally — load gep(%struct.kvm_x86_ops, base, 0, N) — and the
// binding inventory is the set of same-typed global initializers
// (vmx_x86_ops/svm_x86_ops, intel/amd pmu, the apic drivers). Keys
// with any non-conforming update argument (e.g. bpf_dispatcher's JIT
// image) are UNTABLED and their sites keep graph behavior, LOUDLY.
struct SctPending {
  std::string keyName;    // __SCK__<suffix>
  std::string structName; // canonical (suffix-stripped) struct name
  unsigned fieldIdx;
};

extern uint64_t printfSinkCallsites, printfSinkArgsSkipped;
extern uint64_t printfNonConstFmt, printfNonBenignFmt;
extern boost::unordered_flat_set<const Function *> g_noopBodies;
extern bool g_sumAuthoritative;
bool shouldSkipFunction(const Function *F);
StringRef stripStructNameSuffix(StringRef Name);
// Slots.cc: an access's (struct, byte offset), across embedding and -O3.
bool embedsAt(Type *T, int64_t off, StringRef S, const DataLayout &DL);
const GEPOperator *structGEP(const Value *A);
bool accessSlot(const Instruction *I, const Value *Addr, const DataLayout &DL,
                StructType *&S, int64_t &off);
bool tbaaReaches(const Instruction *I, StringRef SN, int64_t o);
// GraphBuild.cc: an inline asm's memory effects as the graph build models
// them (handleInlineAsm adds its edges from this; the container checker
// reads the same model). A value input's `ok`: a pointer, or a
// pointer-width integer witnessed to carry (stores) or become (loads) one.
struct AsmModel {
  struct Value_ {
    const Value *val = nullptr;
    int argIdx = -1;
    bool ok = false, witnessed = false, declined = false;
  };
  struct Slot {
    const Value *ptr = nullptr; // the indirect operand
    int argIdx = -1;
    bool output = false;         // =*m: written with `stores`; *m: read into the result
    std::vector<Value_> stores;  // output: the direct inputs that may be stored
    Value_ load;                 // input: whether the result receives *ptr
  };
  std::vector<Slot> slots;
  bool resPtrCapable = false, resDeclined = false;
  bool memEffects = false;            // a memory clobber or an indirect output
  std::vector<const Value *> rawPtrs; // raw pointer inputs read (and, with memEffects, written)
  std::vector<Value_> valueInputs;    // what a raw pointer input may be written with
};
AsmModel asmModel(const CallBase &CS, const DataLayout *DL);
// ContainerOwnerCode.cc (plan 3.55 R3 D5): in owner code F, the classes of
// values derived from the owner values `owners`: OC_OWNER the owner,
// OC_SLOT a declared slot's address, OC_VAL an element (loaded through a
// slot, a link word decoded, a row's result), OC_WORD a link word.
// slotOf(At, A): the declared slot kind ('h', 'l', 'w') an access at A (At
// the accessing instruction, or null for an address) names, 0 if none.
// rowRet(CB, cls): whether a row call's result is derived given the classes.
// Inlined removes (Fable 2026-10-15): a value whose link read (a LINK field,
// or the LINKWORD decoded) is an element is an element too "under the link
// invariant" (the premise the remove row's ELEM carries); each such value
// goes to *assumed. Owners and elements are identified by object and
// offset: a step from the object to a declared slot whose struct starts at
// an owner's or element's offset is that one's slot (slotStart(A): the
// slot's offset inside its declared struct, -1 if A names none).
enum : uint8_t { OC_OWNER = 1, OC_SLOT = 2, OC_VAL = 4, OC_WORD = 8 };
using OwnerClassFn = std::function<uint8_t(const Value *)>;
std::map<const Value *, uint8_t> deriveOwnerCode(const Function &F, const std::vector<const Value *> &owners,
                                                 const std::vector<const Value *> &elems,
                                                 const std::function<char(const Instruction *, const Value *)> &slotOf,
                                                 const std::function<bool(const CallBase *, const OwnerClassFn &)> &rowRet,
                                                 const DataLayout &DL, StructType *elemT,
                                                 std::vector<const Value *> *assumed,
                                                 const std::function<int64_t(const Value *)> &slotStart);
// The innermost named struct holding byte `off` of T (array members fold
// to their element 0), the offset there, and the scalar the byte lies in
// with the byte's offset inside it. A union on the path stops the name
// (Fable 2026-10-15, class 2): the IR's union type is clang's representative
// member, never the program's, so the name is the struct enclosing the
// union with the byte's offset there, and *inUnion is set.
bool innermostField(Type *T, int64_t off, const DataLayout &DL, std::pair<std::string, int64_t> &K, Type *&leaf,
                    int64_t &inLeaf, bool *inUnion = nullptr);
// The first union on the layout path to byte `off` of T: the union type,
// its start in T and its size.
bool unionOnPath(Type *T, int64_t off, const DataLayout &DL, StructType *&U, int64_t &uOff, int64_t &uSize);
// Does T hold a struct named S at byte `off`, through struct members and
// array elements (each element), never through a union (its IR member is
// clang's representative)?
bool embedsAtThroughArrays(Type *T, int64_t off, StringRef S, const DataLayout &DL);
// An access through a struct's array member at a variable index: the
// member's start stands for the slot.
bool arraySlot(const Value *Addr, const DataLayout &DL, StructType *&S, int64_t &off);
// The struct an address with no struct GEP and no TBAA tag points to (an
// offset-0 access; the kernel builds with -fno-strict-aliasing and carries
// no debug info), in order (Fable 2026-10-15): debug info; a global's or
// local's own IR type (1b: a named struct, or an array of one); sibling GEPs (the
// value is the base of struct GEPs of one struct, after normalizing to the
// innermost struct at offset 0; two structs are a pun: unnamed); a phi whose
// entries agree; a struct GEP's result type; formal provenance (a formal of
// a function whose address is never taken, uses from ".discard*" sections
// excluded, and whose call sites all name one struct). Else unnamed.
class PointeeResolver {
public:
  explicit PointeeResolver(const GlobalContext *Ctx);
  StructType *get(const Value *A, LLVMContext &C, int depth = 0);
  // The innermost named struct at offset 0 of S (timerqueue_node -> rb_node).
  static StructType *atZero(StructType *S);
  // How lookups were decided (counted by get's callers).
  size_t byDI = 0, byDecl = 0, bySibling = 0, byFormal = 0, byBase = 0, pastLayout = 0;
  bool viaFormal = false, viaSibling = false, viaDecl = false; // how the last lookup was decided
  // namedSlot/namedPtr (class 3, Fable 2026-10-15): named by its base's name
  // plus a GEP's byte offset; or a step past the layout of pastS (the base
  // named pastS, the offset pastOff outside [0, sizeof pastS)): unnamed.
  bool viaBase = false, viaResolver = false;
  StructType *pastS = nullptr;
  int64_t pastOff = 0;

private:
  static bool discarded(const User *U);
  std::map<const Function *, std::vector<const CallBase *>> sites;
  std::set<const Function *> taken;
  std::map<const Argument *, StructType *> memo;
  std::set<const Argument *> busy;
};
// The (struct, byte offset) an access names: its struct GEP or TBAA tag
// (accessSlot), an array member at a variable index (arraySlot), or, at
// offset 0 with neither, the address's pointee by the resolver.
bool namedSlot(const Instruction *I, const Value *Addr, const DataLayout &DL, PointeeResolver &P, StructType *&S,
               int64_t &off);
// The (struct, byte offset) a pointer value points into: a constant GEP
// with leading index 0 names its source struct (an array of structs: its
// element); any other constant GEP (a non-zero leading index, a byte GEP)
// contributes only its byte offset to its base's name, which must stay
// inside the base's struct (else a step past the layout: P.pastS); else the
// resolver. A non-zero leading index is never evidence of the base's type.
bool namedPtr(const Value *V, const DataLayout &DL, PointeeResolver &P, StructType *&S, int64_t &off, int depth = 0);
// CellSolver.cc: the debug-info struct ("struct.<tag>") a declared object
// is, or (pointee) a pointer value points to; "" if none.
std::string diDeclaredStruct(const Value *P, bool pointee);
// The indirect calls in IR order (module, function, instruction): the
// context keeps them in a pointer set, whose order follows the heap layout.
std::vector<const CallBase *> icallsInIROrder(const GlobalContext *Ctx);
// The named structs bytes [lo, hi) of T lie in (T itself, members,
// array elements folded to element 0), each with the interval inside it.
void structCover(Type *T, int64_t lo, int64_t hi, const DataLayout &DL,
                 const std::function<void(StructType *, int64_t, int64_t)> &visit);
// The same, stopping at a union (its IR member is clang's representative):
// onUnion gets the union and the interval inside it.
void structCoverToUnions(Type *T, int64_t lo, int64_t hi, const DataLayout &DL,
                         const std::function<void(StructType *, int64_t, int64_t)> &visit,
                         const std::function<void(StructType *, int64_t, int64_t)> &onUnion);
extern size_t g_intStoreUnmodeled;
extern size_t g_intArgUnmodeled;
extern size_t g_initCEDeclined;
extern size_t g_uniEdgeTouches, g_uniDerefTouches, g_uniFptrIcalls;
extern size_t g_rebasedPtrSkipped;
extern boost::unordered_flat_map<NodeIndex, std::string> g_opaqueProvenance;
uint8_t subsysBitOf(const llvm::Module *M2);
extern size_t g_tpKeyConstBinds, g_tpKeyMediatorBinds, g_tpKeyDispatchWires, g_tpKeyUnclassified, g_tpKeyKeylessIter, g_tpKeyUnmapped, g_tpKeyClassFnSkipped, g_tpKeyMediatorDataPools, g_tpKeyIterLoadsSevered;
extern std::vector<const GlobalVariable *> g_tpWalkerKeys;
extern boost::unordered_flat_map<NodeIndex, FuncSet> g_tpKeyProbes;
extern boost::unordered_flat_map<const llvm::CallBase *, NodeIndex> g_tpIterIcallKey;
extern boost::unordered_flat_set<NodeIndex> g_tpKeyHasDynProbe;
extern size_t g_tpKeyModelAnswered, g_tpKeyDynProbe, g_tpKeyFallbackSites, g_tpKeyTypeRej;
extern std::vector<SctPending> g_sctPendings;
extern boost::unordered_flat_map<std::string, FuncSet> g_sctKeyTable;
extern boost::unordered_flat_set<std::string> g_sctKeyUntabled;
extern size_t g_sctUpdConst, g_sctUpdLoad, g_sctUpdNonconform, g_sctTablesScanned, g_sctPendingNoTable, g_sctSitesModelAnswered, g_sctSitesUntabled, g_sctTypeRej;
StringRef sctCanonStructName(StringRef n);
extern size_t g_sinkSitesConfirmed, g_sinkSitesEscaped, g_sinkSitesViolated;
extern bool g_sinkContractChecked;
bool isSinkPayloadAccessor(StringRef n);
extern size_t g_sinkArenaSites;
// --cfl-cells: allocator calls inside kept allocator bodies (no object).
extern size_t g_innerAllocSites;
// --cfl-cells: ptrtoints whose integer never becomes a pointer (no wildcard).
extern size_t g_p2iNumberOnly;
// --cfl-cells: GEPs that carve a new object out of an allocation.
extern size_t g_carves;
extern size_t g_poolCarves;
extern size_t g_dataOnlyGeps; // GEPs whose result is a data pointer (plan 3.42)
// --cfl-cells: deallocator stores into or of the freed block (FREE).
extern size_t g_freeDropped;
extern std::vector<std::pair<NodeIndex, std::string>> g_userCertObjs;
extern size_t g_userCertCopySites, g_userCertGetSites;
extern size_t g_tagRoundTrips;
extern size_t g_staticCallWired, g_staticCallNoKey, g_staticCallUpdates, g_staticCallDynUpdate, g_tracepointProbes, g_staticCallTpIter;
extern size_t g_asmSlotLoads, g_asmSlotStores, g_asmWidthWitnessed, g_asmLaunderDeclined, g_asmRegLoads, g_asmRegStores, g_asmRegCopies;
extern size_t g_intProvStores, g_intProvLoads;
extern size_t g_intLoadUnmodeled;
bool constantHasPtrToInt(const Constant *C, unsigned depth);
bool mayCarryPtrProvenance(const Value *V, unsigned depth, bool &declined);
bool isPtrWidthInt(const Type *T, const DataLayout &DL);
bool linkerBoundsSectionKeys(StringRef N, std::vector<std::string> &exact, std::vector<std::string> &prefix);
bool linkerExcludedFamily(StringRef K);
const AllocaInst *spillSlotOf(const Value *v);
// --cfl-cells carving (GraphBuild.cc): `&a[n]` used as another type starts
// a region of its own; `why` names the other type.
bool carvingGEP(const GetElementPtrInst &GEP, std::string &why);
void reachingSlotStoresOf(const LoadInst *L, const AllocaInst *AI, SmallVectorImpl<const StoreInst *> &out);
void loadFuncSummaries(GlobalContext *Ctx, const std::string &path);
const GlobalContext::FuncSummary * summaryForName(GlobalContext *Ctx, StringRef name, bool hasBody = false);
void walkInitFnOffsets(const Constant *C, uint64_t base, const DataLayout &DL, std::set<int64_t> &out);
void walkInitFnSlots(const Constant *C, uint64_t base, const DataLayout &DL, std::map<uint64_t, const Function *> &out);
void checkFileSummaries(GlobalContext *Ctx);
extern size_t g_sumInvokeRet;
extern size_t g_sumCpy, g_sumAlias, g_sumSt, g_sumLd, g_sumSkipped, g_sumFreshSub, g_sumInvoke, g_sumInvokeDyn, g_chainReg, g_chainRegDyn, g_chainCall, g_chainCallDyn, g_chainLate, g_sumLabels;
extern size_t g_intNameLoads, g_counterRetired, g_counterKept, g_vaMachineryLoads;
bool summaryKeepsBody(GlobalContext *Ctx, const llvm::Function *F);

#endif
