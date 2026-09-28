//===- FlowSensitive.cpp - icalls-fs: FSPTA / VFSPTA / VFPTA call targets -===//
//
// [kanalyzer eval] Backends fspta | vfspta | vfpta, set up exactly like
// tools/alias/lotus-alias-fspta.cpp (its defaults: mutable points-to sets,
// inter-disjoint MemorySSA regions).
//
// fspta / vfspta: the SVFG is built over an AserPTA context-insensitive
// pre-analysis; its indirect calls are connected before solving
// (connectPreAnalysisIndirectCalls) and the solver's on-the-fly connector
// accepts only pre-analysis targets, exactly as the upstream driver does.
// Per site: pointsTo(called operand) mapped through SVFG::getObjectValue to
// Functions. Objects marked unknown carry no function; the solver's own
// connector ignores them, so they add nothing (sidecar "unknown"). A called
// operand with no SVFG value node in scope gives no answer (sidecar
// "no-node").
//
// vfpta: self-contained (no pre-analysis); it builds its call graph on
// the fly from the entry points (default: main) and resolves only
// reachable calls. Per site: getPointsTo(called operand). Its own rule for
// the unknown object is "every defined function" (ValueFlowPTA.cpp: the
// call-graph loop proposes all definitions), which is the answer here
// (sidecar "unknown"; -icalls-no-fill keeps only the Function objects).
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/FlowSensitive/FlowSensitivePTA.h"
#include "Alias/InclusionBased/FlowSensitive/ValueFlowPTA.h"
#include "Alias/InclusionBased/FlowSensitive/VersionedFlowSensitivePTA.h"
#include "IR/ICFG/ICFGBuilder.h"
#include "IR/SVFG/SVFGBuilder.h"

#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <exception>
#include <memory>
#include <optional>

using namespace lotus::alias;
using namespace lotus::analysis;

const char *icalls::backendNames() { return "fspta|vfspta|vfpta"; }

static int runValueFlow(llvm::Module &M) {
  const auto T0 = std::chrono::steady_clock::now();
  ValueFlowPTA Solver(M);
  try {
    Solver.analyze();
  } catch (const std::exception &E) {
    icalls::fatal(llvm::Twine("vfpta failed: ") + E.what());
  }
  const double SolveSec = icalls::secondsSince(T0);
  const auto Unknown = Solver.getUnknownObjectId();
  const auto Null = Solver.getNullObjectId();
  std::vector<const llvm::Function *> Defined;
  for (const llvm::Function &F : M)
    if (!F.isDeclaration())
      Defined.push_back(&F);
  icalls::emit(
      M, "vfpta", {"unknown"},
      [&](llvm::CallBase &CB) {
        icalls::Answer A;
        const auto &Pts = Solver.getPointsTo(CB.getCalledOperand());
        bool HasUnknown = false;
        for (ValueFlowPTA::ObjectID Obj : Pts) {
          if (Obj == Unknown) {
            HasUnknown = true;
            continue;
          }
          if (Obj == Null)
            continue;
          if (auto *F = llvm::dyn_cast_or_null<llvm::Function>(
                  Solver.getObjectValue(Obj)))
            A.Targets.push_back(F);
        }
        if (HasUnknown) {
          A.Reasons.push_back("unknown");
          if (!icalls::noFill())
            A.Targets.insert(A.Targets.end(), Defined.begin(), Defined.end());
        }
        return A;
      },
      SolveSec);
  return 0;
}

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name == "vfpta")
    return runValueFlow(M);
  const bool Versioned = Name == "vfspta";
  if (!Versioned && Name != "fspta")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");

  const auto T0 = std::chrono::steady_clock::now();
  ICFG Icfg;
  ICFGBuilder IcfgBuilder(&Icfg);
  IcfgBuilder.build(&M);
  SVFGBuilderConfig GraphConfig;
  GraphConfig.usePointerAnalysis = true;
  GraphConfig.buildMSSA = true;
  GraphConfig.resolveIndirectCalls = false;
  GraphConfig.memoryPartition = MemoryRegionPartitionStrategy::InterDisjoint;
  auto GraphBuilder = std::make_unique<SVFGBuilder>(GraphConfig);
  std::unique_ptr<SVFG> Graph(GraphBuilder->build(&Icfg));
  if (!Graph)
    fatal("SVFG construction failed");
  GraphBuilder->connectPreAnalysisIndirectCalls(Graph.get());
  auto Connect = [&](const llvm::CallBase *CallSite,
                     const llvm::Function *Target) {
    const std::vector<const llvm::Function *> Allowed =
        GraphBuilder->getIndirectCallTargets(CallSite);
    if (std::find(Allowed.begin(), Allowed.end(), Target) == Allowed.end())
      return false;
    std::vector<SVFGEdge *> Edges;
    return GraphBuilder->connectCallSiteToCalleeOnTheFly(Graph.get(),
                                                         CallSite, Target,
                                                         Edges);
  };
  std::unique_ptr<FlowSensitivePTA> Solver;
  std::unique_ptr<VersionedFlowSensitivePTA> VSolver;
  if (Versioned) {
    VersionedFlowSensitivePTA::Config C;
    C.connectIndirectCall = Connect;
    VSolver = std::make_unique<VersionedFlowSensitivePTA>(*Graph, std::move(C));
    VSolver->solve();
  } else {
    FlowSensitivePTA::Config C;
    C.setBackend = PointsToSetBackend::Mutable;
    C.connectIndirectCall = Connect;
    Solver = std::make_unique<FlowSensitivePTA>(*Graph, std::move(C));
    Solver->solve();
  }
  const double SolveSec = secondsSince(T0);
  auto query = [&](const llvm::Value *V) -> std::optional<SVFGNodeBS> {
    return VSolver ? VSolver->pointsTo(V) : Solver->pointsTo(V);
  };

  emit(M, Name, {"unknown", "no-node"},
       [&](llvm::CallBase &CB) {
         Answer A;
         const llvm::Value *Op = CB.getCalledOperand();
         std::optional<SVFGNodeBS> Pts = query(Op);
         if (!Pts && Op->stripPointerCasts() != Op)
           Pts = query(Op->stripPointerCasts());
         if (!Pts) {
           A.Reasons.push_back("no-node");
           return A;
         }
         bool HasUnknown = false;
         for (uint32_t Obj : *Pts) {
           const SVFG::ObjectInfo *Info = Graph->getObjectInfo(Obj);
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
