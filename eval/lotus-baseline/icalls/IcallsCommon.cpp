//===- IcallsCommon.cpp - per-site indirect-call dump, shared part --------===//
//
// [kanalyzer eval] Driver and JSON/sidecar writer shared by the
// icalls-<family> executables. See IcallsCommon.h for the conventions.
//
// Usage: icalls-<family> -icalls-backend=<name> -icalls-json=<out.json>
//                        [-icalls-include-declarations] [-icalls-no-fill]
//                        [backend flags] <input.bc>
//===----------------------------------------------------------------------===//

#include "IcallsCommon.h"

#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <cstdlib>
#include <map>
#include <set>

namespace cl = llvm::cl;

static cl::opt<std::string> InputFile(cl::Positional, cl::Required,
                                      cl::desc("<input bitcode>"));
static cl::opt<std::string>
    BackendName("icalls-backend", cl::Required,
                cl::desc("Analysis to run (see the tool description)"));
static cl::opt<std::string>
    IcallsJson("icalls-json", cl::Required,
               cl::desc("Write per-site indirect-call targets (JSON); "
                        "sidecars go next to it as <base>.<reason>.sites"));
static cl::opt<bool> IncludeDeclarations(
    "icalls-include-declarations", cl::init(false),
    cl::desc("Keep declared (body-less) callees; default: defined only"));
static cl::opt<bool> NoFillOpt(
    "icalls-no-fill", cl::init(false),
    cl::desc("At fill sites keep only functions present in the points-to "
             "set (the sidecar still lists the site)"));

namespace icalls {

bool noFill() { return NoFillOpt; }

void fatal(const llvm::Twine &Msg) {
  llvm::errs() << "FATAL: " << Msg << "\n";
  std::exit(2);
}

double secondsSince(const std::chrono::steady_clock::time_point &Start) {
  return std::chrono::duration<double>(std::chrono::steady_clock::now() -
                                       Start)
      .count();
}

bool isIndirectSite(const llvm::CallBase &CB) {
  if (CB.isInlineAsm())
    return false;
  return !llvm::isa<llvm::Function>(
      CB.getCalledOperand()->stripPointerCastsAndAliases());
}

std::vector<llvm::CallBase *> collectSites(llvm::Module &M) {
  std::vector<llvm::CallBase *> Sites;
  for (llvm::Function &F : M) {
    if (F.isDeclaration())
      continue;
    for (llvm::Instruction &I : llvm::instructions(F))
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I))
        if (isIndirectSite(*CB))
          Sites.push_back(CB);
  }
  return Sites;
}

std::vector<const llvm::Function *>
addressTakenFunctions(const llvm::Module &M) {
  std::vector<const llvm::Function *> R;
  for (const llvm::Function &F : M)
    if (!F.isIntrinsic() && F.hasAddressTaken())
      R.push_back(&F);
  return R;
}

std::vector<const llvm::Function *> allFunctions(const llvm::Module &M) {
  std::vector<const llvm::Function *> R;
  for (const llvm::Function &F : M)
    if (!F.isIntrinsic())
      R.push_back(&F);
  return R;
}

static std::string siteKey(const llvm::CallBase &CB) {
  const llvm::DebugLoc &DL = CB.getDebugLoc();
  if (!DL)
    return "";
  return (DL->getScope()->getFilename() + ":" + llvm::Twine(DL->getLine()))
      .str();
}

static void writeKeys(llvm::StringRef Path,
                      const std::map<std::string, std::set<std::string>> &M) {
  std::error_code EC;
  llvm::raw_fd_ostream OS(Path, EC, llvm::sys::fs::OF_Text);
  if (EC)
    fatal("cannot write " + Path + ": " + EC.message());
  OS << "{";
  bool FirstK = true;
  for (const auto &KV : M) {
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
}

void emit(llvm::Module &M, llvm::StringRef Backend,
          llvm::ArrayRef<std::string> Reasons, const Resolver &R,
          double SolveSec) {
  const auto T0 = std::chrono::steady_clock::now();
  std::map<std::string, std::set<std::string>> ByLoc;
  std::map<std::string, std::set<std::string>> SideKeys; // reason -> keys
  std::map<std::string, size_t> SideSites;
  for (const std::string &Reason : Reasons) {
    SideKeys[Reason];
    SideSites[Reason] = 0;
  }
  size_t Sites = 0, NoDbg = 0, Unresolved = 0, Edges = 0;
  for (llvm::CallBase *CB : collectSites(M)) {
    Sites++;
    const std::string Key = siteKey(*CB);
    if (Key.empty()) {
      NoDbg++;
      continue;
    }
    std::set<std::string> &Targets = ByLoc[Key];
    const Answer A = R(*CB);
    bool Any = false;
    for (const llvm::Function *F : A.Targets) {
      if (!F)
        fatal("backend " + Backend + " returned a null target");
      if (F->isIntrinsic())
        continue;
      if (F->isDeclaration() && !IncludeDeclarations)
        continue;
      Targets.insert(F->getName().str());
      Any = true;
      Edges++;
    }
    if (!Any)
      Unresolved++;
    for (const std::string &Reason : A.Reasons) {
      auto It = SideKeys.find(Reason);
      if (It == SideKeys.end())
        fatal("backend " + Backend + " used undeclared reason " + Reason);
      It->second.insert(Key);
      SideSites[Reason]++;
    }
  }

  writeKeys(IcallsJson, ByLoc);
  llvm::StringRef Base(IcallsJson);
  Base.consume_back(".json");
  for (const auto &KV : SideKeys) {
    const std::string Path = (Base + "." + KV.first + ".sites").str();
    std::error_code EC;
    llvm::raw_fd_ostream OS(Path, EC, llvm::sys::fs::OF_Text);
    if (EC)
      fatal("cannot write " + Path + ": " + EC.message());
    for (const std::string &K : KV.second)
      OS << K << "\n";
  }

  size_t EmptyKeys = 0, KeyTargets = 0;
  for (const auto &KV : ByLoc) {
    EmptyKeys += KV.second.empty();
    KeyTargets += KV.second.size();
  }
  llvm::errs() << "icalls: backend=" << Backend << " sites=" << Sites
               << " no-dbg=" << NoDbg << " unresolved-sites=" << Unresolved
               << " edges=" << Edges << " keys=" << ByLoc.size()
               << " empty-keys=" << EmptyKeys << " mean-targets-per-key="
               << (ByLoc.empty() ? 0.0
                                 : static_cast<double>(KeyTargets) /
                                       static_cast<double>(ByLoc.size()));
  for (const auto &KV : SideKeys)
    llvm::errs() << " " << KV.first << "-sites=" << SideSites[KV.first] << " "
                 << KV.first << "-keys=" << KV.second.size();
  llvm::errs() << " solve-s=" << SolveSec
               << " dump-s=" << secondsSince(T0) << "\n";
}

} // namespace icalls

int main(int argc, char **argv) {
  llvm::InitLLVM X(argc, argv);
  const std::string Desc = std::string("Lotus per-site indirect-call "
                                       "dumper; -icalls-backend=") +
                           icalls::backendNames() + "\n";
  cl::ParseCommandLineOptions(argc, argv, Desc);

  llvm::LLVMContext Ctx;
  llvm::SMDiagnostic Err;
  std::unique_ptr<llvm::Module> M = llvm::parseIRFile(InputFile, Err, Ctx);
  if (!M) {
    Err.print(argv[0], llvm::errs());
    return 1;
  }
  return icalls::runBackend(*M, BackendName);
}
