//===- GPG.cpp - icalls-gpg: GPG (Gharat/Khedker/Mycroft) call targets ---===//
//
// [kanalyzer eval] Backends gpg-fscs | gpg-fics | gpg-fici select
// GPGConfig::mode (flow- and context-sensitive / flow-insensitive
// context-sensitive / flow- and context-insensitive); every other GPGConfig
// field keeps its default (heap k = 3, field-sensitive, ...).
//
// Answer: GPGResult::callTargets(). Sidecar "fallback": sites whose set was
// still empty after the points-to fixpoint, which GPG then fills with every
// address-taken, signature-compatible function
// (GPGAnalysisEngine::addFallbackIndirectTargets, recorded by
// more-cg-types.patch). GPG keeps fill and later discoveries in one set,
// and a fallback site had no discovered target when it was filled, so
// -icalls-no-fill empties fallback sites.
// Sidecar "no-entry": sites GPG never modelled as an indirect call (no
// entry at all in indirectCallTargets()); they are left empty.
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Alias/InclusionBased/GPG/Analysis.h"

#include <set>

const char *icalls::backendNames() { return "gpg-fscs|gpg-fics|gpg-fici"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  lotus::gpg::GPGConfig Config;
  if (Name == "gpg-fscs")
    Config.mode = lotus::gpg::AnalysisMode::FlowAndContextSensitive;
  else if (Name == "gpg-fics")
    Config.mode = lotus::gpg::AnalysisMode::FlowInsensitiveContextSensitive;
  else if (Name == "gpg-fici")
    Config.mode = lotus::gpg::AnalysisMode::FlowAndContextInsensitive;
  else
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");

  const auto T0 = std::chrono::steady_clock::now();
  lotus::gpg::GPGAnalysisEngine Engine(M, Config);
  Engine.run();
  const double SolveSec = secondsSince(T0);

  const lotus::gpg::GPGResult &Result = Engine.result();
  const std::set<const llvm::CallBase *> &Fallback =
      Engine.fallbackIndirectCalls();
  emit(M, Name, {"fallback", "no-entry"},
       [&](llvm::CallBase &CB) {
         Answer A;
         const std::set<const llvm::Function *> *Targets =
             Result.callTargets(&CB);
         if (!Targets) {
           A.Reasons.push_back("no-entry");
           return A;
         }
         const bool IsFallback = Fallback.count(&CB) != 0;
         if (IsFallback)
           A.Reasons.push_back("fallback");
         if (!(IsFallback && noFill()))
           A.Targets.assign(Targets->begin(), Targets->end());
         return A;
       },
       SolveSec);
  return 0;
}
