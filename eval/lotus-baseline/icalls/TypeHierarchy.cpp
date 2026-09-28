//===- TypeHierarchy.cpp - icalls-th: CHA / RTA / VTA / OTF call graphs ---===//
//
// [kanalyzer eval] Backends cha | rta | vta | otf: Lotus's PhASAR-style
// call-graph resolvers (lib/Analysis/TypeHierarchy), built with
// lotus::buildCallGraph(M, <type>, {"main"}): a worklist from main (or, if
// there is none, every external-linkage definition) that visits only
// reachable functions. They are type/hierarchy-based, not points-to:
// a function-pointer call resolves to every address-taken function that
// passes isConsistentCall (arity, and per parameter/return the same type
// or the same type kind; any pointer matches any pointer); OTF first tries
// a local alias walk and constant global initializers, then falls back to
// that rule; VTA propagates types over a type-assignment graph seeded by
// RTA. Reference rows.
//
// Per site: CallGraph::getCalleesOfCallAt. Sidecar "unreached": sites in
// functions the worklist never visited (empty answer).
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "Analysis/TypeHierarchy/CallGraph.h"
#include "Analysis/TypeHierarchy/CallGraphAnalysisType.h"
#include "Analysis/TypeHierarchy/CallGraphBuilder.h"

#include "llvm/Support/raw_ostream.h"

#include <set>
#include <string>
#include <vector>

const char *icalls::backendNames() { return "cha|rta|vta|otf"; }

int icalls::runBackend(llvm::Module &M, llvm::StringRef Name) {
  lotus::CallGraphAnalysisType Type;
  if (Name == "cha")
    Type = lotus::CallGraphAnalysisType::CHA;
  else if (Name == "rta")
    Type = lotus::CallGraphAnalysisType::RTA;
  else if (Name == "vta")
    Type = lotus::CallGraphAnalysisType::VTA;
  else if (Name == "otf")
    Type = lotus::CallGraphAnalysisType::OTF;
  else
    fatal("unknown backend " + Name + " (expected " + backendNames() + ")");

  const std::vector<std::string> EntryNames = {"main"};
  const auto T0 = std::chrono::steady_clock::now();
  const lotus::CallGraph CG = lotus::buildCallGraph(M, Type, EntryNames);
  const double SolveSec = secondsSince(T0);

  std::set<const llvm::Function *> Visited;
  for (const llvm::Function *F : lotus::getEntryPoints(M, EntryNames))
    Visited.insert(F);
  for (const llvm::Function *F : CG.getAllVertexFunctions())
    Visited.insert(F);
  llvm::errs() << "icalls: " << Name << ": visited-functions="
               << Visited.size() << " cg-call-sites=" << CG.getNumCallSites()
               << "\n";

  emit(M, Name, {"unreached"},
       [&](llvm::CallBase &CB) {
         Answer A;
         if (!Visited.count(CB.getFunction())) {
           A.Reasons.push_back("unreached");
           return A;
         }
         for (const llvm::Function *F : CG.getCalleesOfCallAt(&CB))
           A.Targets.push_back(F);
         return A;
       },
       SolveSec);
  return 0;
}
