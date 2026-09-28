//===- svf-icalls.cpp - per-site indirect-call targets from SVF -----------===//
//
// Runs ONE SVF whole-program pointer analysis and writes the resolved
// targets of every indirect call site in the SoK-MLTA parsed_log key
// space, with the same key/value convention as KAMain's
// --cfl-dump-icalls-json:
//
//   key   = <DILocation scope filename>:<line>   (sites on one line union)
//   value = sorted names of the resolved callees (definitions)
//
// Every indirect call site with a debug location gets a key, including
// sites SVF resolves to nothing, so unresolved sites stay visible.
//
// SVF's own resolution filter is arity only (SVFUtil::matchArgs); this
// tool adds no filter. Resource caps that would silently truncate the
// solve are refused: the run aborts if the resolved-edge budget
// (-ind-call-limit) was reached, instead of emitting a partial answer.
//
// Usage: svf-icalls -icall-pta=ander|fs|vfs|steens -extapi=<extapi.bc>
//                   -icalls-json=<out.json> -ind-call-limit=<N> <bc>
//===----------------------------------------------------------------------===//

#include "SVF-LLVM/LLVMModule.h"
#include "SVF-LLVM/LLVMUtil.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/CommandLine.h"
#include "Util/Options.h"
#include "WPA/Andersen.h"
#include "WPA/FlowSensitive.h"
#include "WPA/Steensgaard.h"
#include "WPA/VersionedFlowSensitive.h"

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/raw_ostream.h"

#include <chrono>
#include <cstdlib>
#include <map>
#include <set>
#include <string>

using namespace SVF;

static Option<std::string> IcallsJson(
    "icalls-json", "Write per-site indirect-call targets (JSON) here", "");
static Option<std::string> IcallPTA(
    "icall-pta", "Pointer analysis: ander | fs | vfs | steens", "ander");

static double secondsSince(std::chrono::steady_clock::time_point T) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - T)
      .count();
}

[[noreturn]] static void fatal(const std::string &Msg) {
  llvm::errs() << "svf-icalls: FATAL: " << Msg << "\n";
  std::exit(2);
}

int main(int argc, char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);
  std::vector<std::string> Mods = OptionBase::parseOptions(
      argc, argv, "svf-icalls: per-site indirect-call targets",
      "[options] <input-bitcode>");
  if (IcallsJson().empty())
    fatal("-icalls-json=<file> is required");
  if (Mods.size() != 1)
    fatal("exactly one input bitcode expected (the linked whole program)");
  // External-function models: without extapi.bc SVF would leave library
  // calls (memcpy, strcpy, ...) unmodeled. Require an explicit, existing
  // path rather than SVF's search, which ends in `npm root`.
  if (Options::ExtAPIPath().empty() ||
      !llvm::sys::fs::exists(Options::ExtAPIPath()))
    fatal("-extapi=<path to SVF's extapi.bc> is required and must exist");

  const auto T0 = std::chrono::steady_clock::now();
  LLVMModuleSet::buildSVFModule(Mods);
  SVFIRBuilder Builder;
  SVFIR *PAG = Builder.build();
  const double BuildSec = secondsSince(T0);

  const auto T1 = std::chrono::steady_clock::now();
  PointerAnalysis *PTA = nullptr;
  const std::string Mode = IcallPTA();
  if (Mode == "ander")
    PTA = AndersenWaveDiff::createAndersenWaveDiff(PAG);
  else if (Mode == "fs")
    PTA = FlowSensitive::createFSWPA(PAG);
  else if (Mode == "vfs")
    PTA = VersionedFlowSensitive::createVFSWPA(PAG);
  else if (Mode == "steens")
    PTA = Steensgaard::createSteensgaard(PAG);
  else
    fatal("unknown -icall-pta=" + Mode);
  const double SolveSec = secondsSince(T1);

  // A reached budget means resolution stopped early: refuse, never emit
  // a truncated answer as if it were the analysis result.
  const u32_t Resolved = PTA->getNumOfResolvedIndCallEdge();
  if (Resolved >= Options::IndirectCallLimit())
    fatal("resolved indirect-call edges reached -ind-call-limit (" +
          std::to_string(Options::IndirectCallLimit()) +
          "); rerun with a larger limit");

  LLVMModuleSet *MS = LLVMModuleSet::getLLVMModuleSet();
  const PointerAnalysis::CallEdgeMap &IndMap = PTA->getIndCallMap();

  std::map<std::string, std::set<std::string>> ByLoc;
  size_t Sites = 0, NoDbg = 0, Unresolved = 0, Edges = 0;
  for (llvm::Module &M : MS->getLLVMModules()) {
    for (llvm::Function &F : M) {
      if (F.isDeclaration())
        continue;
      for (llvm::Instruction &I : llvm::instructions(F)) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || CB->isInlineAsm())
          continue;
        if (llvm::isa<llvm::Function>(
                CB->getCalledOperand()->stripPointerCasts()))
          continue;
        Sites++;
        const llvm::DebugLoc &DL = CB->getDebugLoc();
        if (!DL) {
          NoDbg++;
          continue;
        }
        const std::string Key = (DL->getScope()->getFilename() + ":" +
                                 llvm::Twine(DL->getLine()))
                                    .str();
        std::set<std::string> &Targets = ByLoc[Key];
        const CallICFGNode *CN = MS->getCallICFGNode(CB);
        auto It = IndMap.find(CN);
        if (It == IndMap.end() || It->second.empty()) {
          Unresolved++;
          continue;
        }
        for (const FunObjVar *Callee : It->second) {
          const FunObjVar *Def = Callee->getDefFunForMultipleModule();
          Targets.insert((Def ? Def : Callee)->getName());
          Edges++;
        }
      }
    }
  }

  std::error_code EC;
  llvm::raw_fd_ostream OS(IcallsJson(), EC, llvm::sys::fs::OF_Text);
  if (EC)
    fatal("cannot write " + IcallsJson() + ": " + EC.message());
  OS << "{";
  bool FirstK = true;
  for (const auto &KV : ByLoc) {
    OS << (FirstK ? "" : ",") << "\n  \"";
    FirstK = false;
    OS.write_escaped(KV.first);
    OS << "\": [";
    bool FirstT = true;
    for (const std::string &T : KV.second) {
      OS << (FirstT ? "" : ", ") << "\"";
      FirstT = false;
      OS.write_escaped(T);
      OS << "\"";
    }
    OS << "]";
  }
  OS << "\n}\n";
  OS.close();

  llvm::errs() << "svf-icalls: pta=" << Mode << " sites=" << Sites
               << " keys=" << ByLoc.size() << " no-dbg=" << NoDbg
               << " unresolved=" << Unresolved << " site-edges=" << Edges
               << " resolved-edges=" << Resolved << " build-s=" << BuildSec
               << " solve-s=" << SolveSec << "\n";

  LLVMModuleSet::releaseLLVMModuleSet();
  return 0;
}
