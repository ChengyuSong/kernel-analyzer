//===- DDA.cpp - icalls-dda: demand-driven FlowDDA call targets -----------===//
//
// [kanalyzer eval] Backend dda-flow: Lotus FlowDDA (SVF-style demand-driven
// flow-sensitive, context-insensitive analysis on an SVFG over an AserPTA
// context-insensitive pre-analysis; indirect-call edges are added on the
// fly as function-pointer queries resolve). This is what DDAPass with
// DDAKind::FlowS_DDA and the Funptr client does: one getPointsTo query per
// indirect call's called operand, in module order. The per-query step
// budget is -icalls-dda-budget (Lotus default 100000).
//
// Per site: the query's objects mapped through SVFG::getObjectValue to
// Functions (DDA's own connectIndirectCallees uses exactly these; unknown
// objects connect nothing).
//   budget exhausted   the query's answer is FlowDDA's conservative
//                      fallback (getConservativeCPts); sidecar "budget"
//   unknown object     sidecar "unknown" (adds no function)
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/DemandDriven/DDA/FlowDDA.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <set>

namespace cl = llvm::cl;

static cl::opt<unsigned>
    Budget("icalls-dda-budget", cl::init(100000),
           cl::desc("FlowDDA steps per query before the conservative "
                    "fallback"));

const char *icalls::backendNames() { return "dda-flow"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name != "dda-flow")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");

  const auto T0 = std::chrono::steady_clock::now();
  lotus::analysis::FlowDDA::setDefaultMaxBudget(Budget);
  lotus::analysis::FlowDDA DDA;
  if (!DDA.run(M))
    fatal("FlowDDA initialization (ICFG/SVFG) failed");
  const double BuildSec = secondsSince(T0);

  // A query answered from FlowDDA's value cache does not reset the budget
  // flag, so the flag is cleared before each query and a value's
  // out-of-budget status is remembered from the query that computed it.
  std::set<const llvm::Value *> OutOfBudget;
  auto query = [&](const llvm::CallBase &CB) {
    const llvm::Value *Op = CB.getCalledOperand();
    DDA.setOutOfBudget(false);
    auto Pts = DDA.getPointsTo(Op);
    if (DDA.isOutOfBudget())
      OutOfBudget.insert(Op->stripPointerCasts());
    return Pts;
  };
  // The Funptr client's pass: every indirect call, keyed or not.
  const std::vector<llvm::CallBase *> Sites = collectSites(M);
  for (llvm::CallBase *CB : Sites)
    (void)query(*CB);
  const double SolveSec = secondsSince(T0);
  llvm::errs() << "icalls: dda-flow: budget=" << Budget
               << " build-s=" << BuildSec << " queries=" << Sites.size()
               << " out-of-budget-values=" << OutOfBudget.size() << "\n";

  const lotus::analysis::SVFG *Graph = DDA.getSVFGConst();
  emit(M, Name, {"budget", "unknown"},
       [&](llvm::CallBase &CB) {
         Answer A;
         // Cached unless an on-the-fly edge added since invalidated it.
         const auto Pts = query(CB);
         if (OutOfBudget.count(CB.getCalledOperand()->stripPointerCasts()))
           A.Reasons.push_back("budget");
         bool HasUnknown = false;
         for (uint32_t Obj : Pts) {
           const auto *Info = Graph->getObjectInfo(Obj);
           if (Info && Info->isUnknown)
             HasUnknown = true;
           if (auto *F = llvm::dyn_cast_or_null<llvm::Function>(
                   Graph->getObjectValue(Obj)))
             A.Targets.push_back(F);
         }
         if (HasUnknown)
           A.Reasons.push_back("unknown");
         return A;
       },
       SolveSec);
  return 0;
}
