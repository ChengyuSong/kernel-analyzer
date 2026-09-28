//===- seadsa-icalls.cpp - per-site indirect-call targets from SeaDsa -----===//
//
// Runs SeaDsa's CompleteCallGraph (context-sensitive, unification-based,
// heap cloning) with the same pass pipeline as Lotus's
// lotus-alias-seadsa-tool (RemovePtrToInt, AllocWrapInfo,
// DsaLibFuncInfo), and writes per-site targets in the SoK parsed_log key
// space ("<DILocation scope filename>:<line>" -> callee names), the
// convention of KAMain --cfl-dump-icalls-json.
//
// SeaDsa marks each indirect call site complete or not. Incomplete sites
// are written with their (partial) targets and listed separately, so the
// reader can see where SeaDsa itself does not claim a full answer.
//
// Usage: seadsa-icalls -icalls-json=<out.json>
//                      [-incomplete-list=<out.txt>] <bc>
//===----------------------------------------------------------------------===//

#include "Alias/Infrastructure/AliasAnalysisWrapper/CLIUtils.h"
#include "Alias/UnificationBased/seadsa/CompleteCallGraph.hh"
#include "Alias/UnificationBased/seadsa/DsaLibFuncInfo.hh"
#include "Alias/UnificationBased/seadsa/InitializePasses.hh"
#include "Alias/UnificationBased/seadsa/support/RemovePtrToInt.hh"

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/InitializePasses.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <chrono>
#include <cstdlib>
#include <map>
#include <set>
#include <string>

namespace cl = llvm::cl;

static cl::opt<std::string> InputFile(cl::Positional, cl::Required,
                                      cl::desc("<input bitcode>"));
static cl::opt<std::string>
    IcallsJson("icalls-json", cl::Required,
               cl::desc("Write per-site indirect-call targets (JSON)"));
static cl::opt<std::string>
    IncompleteList("incomplete-list", cl::init(""),
                   cl::desc("Write keys of sites SeaDsa marks incomplete"));

int main(int argc, char **argv) {
  llvm::InitLLVM X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "seadsa-icalls\n");

  llvm::LLVMContext Ctx;
  llvm::SMDiagnostic Err;
  std::unique_ptr<llvm::Module> M =
      lotus::alias::tools::loadIRModule(InputFile, Ctx, Err, argv[0]);
  if (!M)
    return 1;

  const auto T0 = std::chrono::steady_clock::now();
  llvm::PassRegistry &Registry = *llvm::PassRegistry::getPassRegistry();
  llvm::initializeCore(Registry);
  llvm::initializeAnalysis(Registry);
  seadsa::initializeAnalysisPasses(Registry);
  // seadsa::initializeAnalysisPasses registers only LLVM's own passes;
  // SeaDsa's immutable passes must be registered too, or the legacy
  // pass manager dereferences a null PassInfo when scheduling them.
  llvm::initializeRemovePtrToIntPass(Registry);
  llvm::initializeAllocWrapInfoPass(Registry);
  llvm::initializeDsaLibFuncInfoPass(Registry);
  llvm::initializeCompleteCallGraphPass(Registry);

  llvm::legacy::PassManager PM;
  PM.add(new seadsa::RemovePtrToInt());
  PM.add(new seadsa::AllocWrapInfo());
  PM.add(new seadsa::DsaLibFuncInfo());
  auto *CCG = new seadsa::CompleteCallGraph();
  PM.add(CCG);
  PM.run(*M);
  const double SolveSec =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - T0)
          .count();

  std::map<std::string, std::set<std::string>> ByLoc;
  std::set<std::string> IncompleteKeys;
  size_t Sites = 0, NoDbg = 0, Unresolved = 0, Incomplete = 0;
  for (llvm::Function &F : *M) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F)) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || CB->isInlineAsm())
        continue;
      if (llvm::isa<llvm::Function>(
              CB->getCalledOperand()->stripPointerCastsAndAliases()))
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
      if (!CCG->isComplete(*CB)) {
        Incomplete++;
        IncompleteKeys.insert(Key);
      }
      bool Any = false;
      for (auto It = CCG->begin(*CB), E = CCG->end(*CB); It != E; ++It) {
        if (*It) {
          Targets.insert((*It)->getName().str());
          Any = true;
        }
      }
      if (!Any)
        Unresolved++;
    }
  }

  std::error_code EC;
  llvm::raw_fd_ostream OS(IcallsJson, EC, llvm::sys::fs::OF_Text);
  if (EC) {
    llvm::errs() << "FATAL: cannot write " << IcallsJson << ": "
                 << EC.message() << "\n";
    return 2;
  }
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

  if (!IncompleteList.empty()) {
    llvm::raw_fd_ostream IL(IncompleteList, EC, llvm::sys::fs::OF_Text);
    if (EC) {
      llvm::errs() << "FATAL: cannot write " << IncompleteList << "\n";
      return 2;
    }
    for (const std::string &K : IncompleteKeys)
      IL << K << "\n";
  }

  llvm::errs() << "seadsa-icalls: sites=" << Sites << " keys=" << ByLoc.size()
               << " no-dbg=" << NoDbg << " unresolved=" << Unresolved
               << " incomplete=" << Incomplete << " solve-s=" << SolveSec
               << "\n";
  return 0;
}
