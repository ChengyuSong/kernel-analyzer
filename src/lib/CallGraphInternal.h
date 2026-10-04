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
void reachingSlotStoresOf(const LoadInst *L, const AllocaInst *AI, SmallVectorImpl<const StoreInst *> &out);
void loadFuncSummaries(GlobalContext *Ctx, const std::string &path);
const GlobalContext::FuncSummary * summaryForName(GlobalContext *Ctx, StringRef name, bool hasBody = false);
void walkInitFnOffsets(const Constant *C, uint64_t base, const DataLayout &DL, std::set<int64_t> &out);
void walkInitFnSlots(const Constant *C, uint64_t base, const DataLayout &DL, std::map<uint64_t, const Function *> &out);
void checkFileSummaries(GlobalContext *Ctx);
extern size_t g_sumInvokeRet;
extern size_t g_sumCpy, g_sumAlias, g_sumSt, g_sumLd, g_sumSkipped, g_sumFreshSub, g_sumInvoke, g_sumInvokeDyn, g_chainReg, g_chainRegDyn, g_chainCall, g_chainCallDyn, g_chainLate;
bool summaryInvokeKeepsBody(GlobalContext *Ctx, const llvm::Function *F);

#endif
