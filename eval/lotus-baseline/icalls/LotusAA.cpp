//===- LotusAA.cpp - icalls-lotusaa: LotusAA call targets, caps lifted ---===//
//
// [kanalyzer eval] Backend lotusaa. LotusAA resolves indirect calls only
// when it builds its own call graph (-lotus-cg, default off) and only on
// the iterative path (-lotus-aa-fixed-cg=false; the default fixed-CG path
// never calls computeCG and returns no indirect target). Its defaults also
// cap the analysis in ways that DROP targets without a warning. This tool
// refuses to run unless every cap is lifted on the command line:
//
//   -lotus-cg -lotus-aa-fixed-cg=false
//   -lotus-restrict-cg-iter=1000000        (default 2: stops before fixpoint)
//   -lotus-restrict-pts-count=-1           (default 3: loads through a
//                                           pointer with >3 pointees yield
//                                           nothing)
//   -lotus-restrict-right-value-count=-1   (default 100)
//   -lotus-timeout=1000000000              (default 10 s/function: results
//                                           cleared, function = library)
//   -lotus-restrict-cg-size=1000000        (default 5 callees applied)
//   -lotus-restrict-output-pts=-1          (default 10)
//   -lotus-restrict-summary-ap-depth=100   (default 10; clamped to 100)
//   -lotus-restrict-obj-ap-depth=10000     (default 5; a BFS depth, no
//                                           sentinel)
//   -lotus-restrict-memory-max-bb-load=-1 -lotus-restrict-memory-max-bb-depth=-1
//   -lotus-restrict-memory-max-load=-1    -lotus-restrict-memory-store-depth=-1
//   -lotus-restrict-inline-depth: default -2 (unbounded) or any negative
//
// and it lifts the two caps that have no flag itself
// (IntraLotusAAConfig::lotus_restrict_inline_size = -1,
//  lotus_restrict_ap_level = 0: keep every interface node).
// -icalls-lotus-allow-caps skips the check (for experiments only).
//
// Answer: FunctionPointerResults, keyed by the CallBase. No fill exists;
// sidecar "no-entry": sites LotusAA recorded no result for. NOTE (upstream
// behavior, not a cap): IntraLotusAA walks only the blocks a Kahn
// topological sort of the CFG reaches (topSortCFG in
// IntraProceduralAnalysis.cpp), so every block on or after a CFG cycle is
// never analyzed; calls in loops and after loops are "no-entry".
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/LotusAA/Engine/InterProceduralPass.h"
#include "Alias/InclusionBased/LotusAA/Engine/IntraProceduralAnalysis.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <set>

namespace cl = llvm::cl;

static cl::opt<bool> AllowCaps(
    "icalls-lotus-allow-caps", cl::init(false),
    cl::desc("Run LotusAA even if some cap is not lifted (not for eval)"));

template <typename T> static T optionValue(llvm::StringRef Name) {
  auto &Opts = cl::getRegisteredOptions();
  auto It = Opts.find(Name);
  if (It == Opts.end())
    icalls::fatal("LotusAA option -" + Name + " is not registered");
  return static_cast<cl::opt<T> *>(It->second)->getValue();
}

static void checkUncapped() {
  std::vector<std::string> Bad;
  auto need = [&](bool Ok, const std::string &What) {
    if (!Ok)
      Bad.push_back(What);
  };
  need(optionValue<bool>("lotus-cg"), "-lotus-cg");
  need(!optionValue<bool>("lotus-aa-fixed-cg"), "-lotus-aa-fixed-cg=false");
  need(optionValue<int>("lotus-restrict-cg-iter") >= 1000000,
       "-lotus-restrict-cg-iter>=1000000");
  need(optionValue<int>("lotus-restrict-pts-count") == -1,
       "-lotus-restrict-pts-count=-1");
  need(optionValue<int>("lotus-restrict-right-value-count") == -1,
       "-lotus-restrict-right-value-count=-1");
  need(optionValue<double>("lotus-timeout") >= 1e9, "-lotus-timeout>=1e9");
  need(optionValue<int>("lotus-restrict-cg-size") >= 1000000,
       "-lotus-restrict-cg-size>=1000000");
  need(optionValue<int>("lotus-restrict-output-pts") == -1,
       "-lotus-restrict-output-pts=-1");
  need(optionValue<int>("lotus-restrict-summary-ap-depth") >= 100,
       "-lotus-restrict-summary-ap-depth=100");
  need(optionValue<int>("lotus-restrict-obj-ap-depth") >= 10000,
       "-lotus-restrict-obj-ap-depth>=10000");
  for (const char *Name :
       {"lotus-restrict-memory-max-bb-load", "lotus-restrict-memory-max-bb-depth",
        "lotus-restrict-memory-max-load", "lotus-restrict-memory-store-depth"})
    need(optionValue<int>(Name) == -1, std::string("-") + Name + "=-1");
  need(optionValue<int>("lotus-restrict-inline-depth") < 0,
       "-lotus-restrict-inline-depth<0");
  if (Bad.empty())
    return;
  std::string Msg = "LotusAA caps not lifted:";
  for (const std::string &B : Bad)
    Msg += " " + B;
  if (AllowCaps) {
    llvm::errs() << "WARNING: " << Msg << " (-icalls-lotus-allow-caps)\n";
    return;
  }
  icalls::fatal(Msg + " (or pass -icalls-lotus-allow-caps)");
}

const char *icalls::backendNames() { return "lotusaa"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  if (Name != "lotusaa")
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");
  checkUncapped();
  if (!AllowCaps) {
    llvm::IntraLotusAAConfig::lotus_restrict_inline_size = -1;
    llvm::IntraLotusAAConfig::lotus_restrict_ap_level = 0;
  }

  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeCore(Registry);
  llvm::initializeAnalysis(Registry);

  const auto T0 = std::chrono::steady_clock::now();
  llvm::legacy::PassManager PM; // owns the pass; keep alive while reading
  auto *Pass = new llvm::LotusAA();
  PM.add(Pass);
  PM.run(M);
  const double SolveSec = secondsSince(T0);

  std::map<const llvm::CallBase *, std::set<const llvm::Function *>> Targets;
  size_t NonCallKeys = 0;
  for (const auto &CallerResults :
       Pass->getFunctionPointerResults().getResultsMap()) {
    for (const auto &SiteResults : CallerResults.second) {
      const llvm::Value *Site = SiteResults.first;
      std::vector<const llvm::CallBase *> Calls;
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(Site)) {
        Calls.push_back(CB);
      } else {
        // Keyed by a called operand (not seen in 0da4c281): every call of
        // the caller through it gets the targets.
        ++NonCallKeys;
        for (const llvm::User *U : Site->users())
          if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
            if (CB->getCalledOperand() == Site)
              Calls.push_back(CB);
      }
      for (const llvm::CallBase *CB : Calls) {
        auto &S = Targets[CB];
        for (const auto &Item : SiteResults.second)
          if (Item.first)
            S.insert(Item.first);
      }
    }
  }
  if (NonCallKeys)
    llvm::errs() << "icalls: lotusaa: " << NonCallKeys
                 << " result keys were called operands, not calls\n";

  emit(M, Name, {"no-entry"},
       [&](llvm::CallBase &CB) {
         Answer A;
         auto It = Targets.find(&CB);
         if (It == Targets.end()) {
           A.Reasons.push_back("no-entry");
           return A;
         }
         A.Targets.assign(It->second.begin(), It->second.end());
         return A;
       },
       SolveSec);
  return 0;
}
