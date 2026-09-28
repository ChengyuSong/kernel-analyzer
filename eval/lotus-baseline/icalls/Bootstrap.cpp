//===- Bootstrap.cpp - icalls-bootstrap: BootstrapAA call targets ---------===//
//
// [kanalyzer eval] Backend bootstrap (Kahlon PLDI'08 framework: Steensgaard
// partitions, thresholded Andersen refinement, flow- and context-sensitive
// per-cluster solving). Closed world from the entry (default: main; the
// analysis refuses a module without a defined main). Run single-threaded
// (parallel_clusters off); every other Options field keeps its default,
// including the resource guards (max_contexts 4096, max_steps 1e6), which
// yield top, never a partial set.
//
// Per site: pointsToAllContexts(called operand) after the operand's
// defining instruction (before the call for a non-instruction operand). Function
// objects map back to their llvm::Function.
//   status Unreachable            empty; sidecar "unreachable"
//   status ResourceLimit          sidecar "resource-limit"; answer = top
//   top (UNKNOWN in the set)      sidecar "top"; answer = every function
//                                 (the engine's own rule for a top callee:
//                                 Engine.cpp callees())
//   operand not modelled (throws) empty; sidecar "unmodelled"
// -icalls-no-fill keeps only the Function objects at top sites.
// NOTE (upstream behavior): at 0da4c281 every pointer LOADED from memory
// evaluates to top (checked with -icalls-bootstrap-debug, which prints
// lotus-alias-bootstrap's per-instruction listing, on O0 and mem2reg'd
// test code), so nearly every indirect call is a "top" site.
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/BootstrapAA/BootstrapAA.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <exception>
#include <memory>
#include <stdexcept>

namespace bs = lotus::bootstrap;

static llvm::cl::opt<bool>
    DebugPts("icalls-bootstrap-debug", llvm::cl::init(false),
             llvm::cl::desc("Print every pointer instruction's points-to"));

const char *icalls::backendNames() { return "bootstrap"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name != "bootstrap")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");

  const auto T0 = std::chrono::steady_clock::now();
  bs::Options Opts;
  Opts.parallel_clusters = false;
  Opts.parallelism = 1;
  std::unique_ptr<bs::BootstrapAA> AA;
  try {
    AA = std::make_unique<bs::BootstrapAA>(M, nullptr, Opts);
  } catch (const std::exception &E) {
    fatal(llvm::Twine("BootstrapAA setup failed: ") + E.what());
  }
  const double SetupSec = secondsSince(T0);

  if (DebugPts) { // lotus-alias-bootstrap's listing, all contexts
    for (const llvm::Function &F : M)
      for (const llvm::BasicBlock &BB : F)
        for (const llvm::Instruction &I : BB) {
          if (!I.getType()->isPointerTy())
            continue;
          bs::QueryResult R = AA->pointsToAllContexts(I, I, bs::Point::After);
          llvm::errs() << F.getName() << ": " << I << " -> status="
                       << static_cast<int>(R.status)
                       << " top=" << R.points_to.isTop() << " {";
          for (bs::Id O : R.points_to)
            llvm::errs() << " " << AA->objectInfo(O).name;
          llvm::errs() << " }\n";
        }
  }
  const std::vector<const llvm::Function *> All = allFunctions(M);
  double QuerySec = 0; // queries solve clusters on demand
  emit(M, Name, {"unreachable", "resource-limit", "top", "unmodelled"},
       [&](llvm::CallBase &CB) {
         Answer A;
         const auto Q0 = std::chrono::steady_clock::now();
         bs::QueryResult R;
         try {
           // Query the operand where it is defined (after its defining
           // instruction), as lotus-alias-bootstrap does; the engine
           // answers top for a value outside its slice at a program
           // point, so querying "before the call" can lose it.
           const llvm::Value *Op = CB.getCalledOperand();
           if (auto *Def = llvm::dyn_cast<llvm::Instruction>(Op))
             R = AA->pointsToAllContexts(*Op, *Def, bs::Point::After);
           else
             R = AA->pointsToAllContexts(*Op, CB, bs::Point::Before);
         } catch (const std::invalid_argument &) {
           A.Reasons.push_back("unmodelled");
           QuerySec += secondsSince(Q0);
           return A;
         }
         QuerySec += secondsSince(Q0);
         if (R.status == bs::QueryStatus::Unreachable) {
           A.Reasons.push_back("unreachable");
           return A;
         }
         const bool Limit = R.status == bs::QueryStatus::ResourceLimit;
         const bool Top = Limit || R.points_to.isTop();
         if (Limit)
           A.Reasons.push_back("resource-limit");
         else if (Top)
           A.Reasons.push_back("top");
         for (bs::Id Obj : R.points_to) {
           if (Obj == bs::UNKNOWN || Obj == bs::NULL_OBJECT)
             continue;
           if (AA->objectInfo(Obj).kind != bs::ObjectKind::Function)
             continue;
           if (auto *F = llvm::dyn_cast_or_null<llvm::Function>(
                   AA->allocationSite(Obj)))
             A.Targets.push_back(F);
         }
         if (Top && !noFill())
           A.Targets = All;
         return A;
       },
       SetupSec);
  llvm::errs() << "icalls: bootstrap: setup-s=" << SetupSec
               << " query-s=" << QuerySec << "\n";
  return 0;
}
