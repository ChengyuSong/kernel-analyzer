/*
 * KAMain: indirect-call resolution with the rooted flows-to solver.
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 Byoungyoung Lee
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/PrettyStackTrace.h>

#include <chrono>
#include <string>
#include <vector>

#include "CallGraph.h"
#include "Driver.h"
#include "IRSidecar.h"

using namespace llvm;

#define Diag llvm::errs()

// Options removed when KAMain became the flows-to solver only
// (docs/release-trim.md, 2026-10-02). Passing one is an error.
static const RemovedFlag RemovedFlags[] = {
  {"cfl-flows-to", "the flows-to solver is KAMain's only mode; drop the flag"},
  {"cfl-compositional", "compositional saturation moved to the CFL "
                        "baseline (KABaseline); KAMain is the flows-to "
                        "solver only, drop the flag"},
  {"cfl-compressed-output", "moved to the CFL baseline (KABaseline)"},
  {"cfl-compressed-input", "moved to the CFL baseline (KABaseline)"},
  {"cfl-presolve-merge", "KAMain always pre-solves; the opt-in saturation "
                         "presolve moved to the CFL baseline (KABaseline)"},
  {"cfl-fptr-slice", "moved to the CFL baseline (KABaseline)"},
  {"grammar-file", "the grammar drives the CFL baseline only (KABaseline)"},
  {"cfl-edge-output", "GraCFL edge files are written by the CFL baseline "
                      "(KABaseline --cfl-edge-output)"},
  {"v-snapshot", "moved to the CFL baseline (KABaseline)"},
  {"cfl-cache-strict", "moved to the CFL baseline (KABaseline)"},
  {"cfl-cache-repair", "moved to the CFL baseline (KABaseline)"},
  {"cfl-cache-allow-duplicate-coverage",
   "moved to the CFL baseline (KABaseline)"},
  {"llm-server-host", "KAMain no longer queries an LLM"},
  {"llm-server-port", "KAMain no longer queries an LLM"},
  {"query-llm", "KAMain no longer queries an LLM"},
  {"invoke-proposals", "KAMain no longer mines kerneldoc with an LLM"},
  {"invoke-mine-dry", "KAMain no longer mines kerneldoc with an LLM"},
  {"kernel-src", "only the removed kerneldoc mining used it"},
  {"allocator-file", "allocators come from --func-summaries (FRESH)"},
  {"container-file", "containers come from --func-summaries"},
  {"cfl-probe-no-cell-identity",
   "retired measurement probe; its finding is recorded in docs/release-trim.md (flag census)"},
  {"cfl-probe-no-x-bridges",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-identity-join-ablate",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-wildcard-ablate",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-stratum-ablate",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-usercopy-ablate",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-no-icall-wiring",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-no-int-stores",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-noformal-presolve",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-born-hub",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-witness-sep",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-blob-grep",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-sink-ablate",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-no-trans-join",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-ops-mono",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
  {"cfl-probe-origin-split",
   "retired measurement probe; finding in docs/release-trim.md (flag census)"},
};

int main(int argc, char **argv) {
  kaStartProcess(argc, argv);
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  kaRefuseRemovedFlags(argc, argv, RemovedFlags);
  cl::ParseCommandLineOptions(
      argc, argv, "KAMain: indirect-call resolution (flows-to solver)\n");

  if (int rc = kaReadInputList(argv[0]))
    return rc;

  // CLI sanity: reject option combinations the solver cannot honor
  // exactly. A misconfigured whole-kernel run wastes tens of minutes
  // before the mismatch surfaces — fail here.
  {
    std::vector<std::string> cliErrors;

    if (CFLBatchRoots > 0 && CFLLazyMint) {
      errs() << "ERROR: --cfl-batch-roots is incompatible with "
                "--cfl-lazy-mint (deferred-root admission assumes live "
                "planes across the whole drain)\n";
      exit(1);
    }
    if (CFLBatchRoots > 0 && CFLVerifyClosure) {
      errs() << "ERROR: --cfl-batch-roots releases planes between "
                "batches; --cfl-verify-closure would check only the "
                "last batch and report false violations\n";
      exit(1);
    }
    if (!CFLBatchSpill.empty() && CFLBatchRoots == 0) {
      errs() << "ERROR: --cfl-batch-spill requires --cfl-batch-roots "
                "(spill files are per-batch plane snapshots)\n";
      exit(1);
    }
    if (CFLBatchWorkers > 1 && CFLBatchRoots == 0) {
      errs() << "ERROR: --cfl-batch-workers requires --cfl-batch-roots "
                "(the batch size defines what each worker solves)\n";
      exit(1);
    }
    if (CFLChannelCells) {
      if (CFLBatchRoots > 0) {
        errs() << "ERROR: --cfl-channel-cells v1 is mono-solve only "
                  "(batch event replay records cluster joins; the "
                  "channel analog is edge additions — not ported yet)\n";
        exit(1);
      }
      if (CFLVerifyClosure) {
        errs() << "ERROR: --cfl-channel-cells v1 does not support "
                  "--cfl-verify-closure (C4-key mirrors the cluster "
                  "join rule; the verifier must mirror the channel "
                  "rule before certifying)\n";
        exit(1);
      }
      if (CFLSolverThreads > 1) {
        errs() << "ERROR: --cfl-channel-cells v1 requires a sequential "
                  "solve (pend flush and node growth are barrier-"
                  "serial)\n";
        exit(1);
      }
    }
    if (CFLKeyChannels && !CFLChannelCells) {
      const bool mono = CFLBatchRoots == 0 && CFLSolverThreads <= 1 &&
                        !CFLVerifyClosure;
      if (!mono) {
        if (CFLKeyChannels.getNumOccurrences() > 0) {
          errs() << "ERROR: --cfl-key-channels needs the sequential mono "
                    "solve (no batch roots, one solver thread, no "
                    "--cfl-verify-closure): the pend flush and node growth "
                    "are barrier-serial\n";
          exit(1);
        }
        CFLKeyChannels = false;
        errs() << "KeyChannels: OFF (batch/parallel/verify-closure solve; "
                  "constant-global keys merge as clusters)\n";
      }
    }
    if (CFLIdentityChannels && !CFLKeyChannels) {
      if (CFLKeyChannels.getNumOccurrences() > 0) {
        errs() << "ERROR: --cfl-identity-channels needs --cfl-key-channels\n";
        exit(1);
      }
      CFLKeyChannels = true;
    }
    if (!CFLNexusFields.empty() && CFLFieldBuckets == 0) {
      if (CFLFieldBuckets.getNumOccurrences() == 0) {
        CFLFieldBuckets = 13;
        errs() << "NexusFields: --cfl-field-buckets unset, using 13\n";
      } else {
        errs() << "ERROR: --cfl-nexus-fields requires "
                  "--cfl-field-buckets>0 (residue planes carry the "
                  "nexus precision)\n";
        exit(1);
      }
    }
    if (CFLPreSolveExact && CFLPreSolveCone) {
      errs() << "ERROR: --cfl-presolve-exact and --cfl-presolve-cone are "
                "mutually exclusive\n";
      exit(1);
    }
    if (CFLStaticOpsTables && !CFLStaticCall) {
      if (CFLStaticOpsTables.getNumOccurrences() == 0) {
        CFLStaticOpsTables = false; // no static-call model, no keys
      } else {
        errs() << "ERROR: --cfl-static-ops-tables requires "
                  "--cfl-static-call\n";
        exit(1);
      }
    }
    if (CFLLazyAddress) {
      CFLChannelCells = true; // storage identity = the address channel
      if (CFLFieldBuckets == 0) CFLFieldBuckets = 13; // f-edge labels only
      if (CFLBatchRoots > 0 || CFLVerifyClosure)
        cliErrors.push_back("--cfl-lazy-address refuses batch mode and "
                            "the closure verifier (single plane, exact "
                            "labels)");
      CFLBidiPrune = false; // cone is residue-based; not ported
    }
    if (CFLChannelCells && CFLKeyIdentity.getNumOccurrences() == 0) {
      // Channel cells carry the identity of never-written content on
      // the channel key (docs/channel-cells-design.md, "Identity of
      // unwritten content"); per-access cell roots are the old model.
      // Default it on whenever channels exist; --cfl-key-identity=false
      // restores per-access roots for comparison.
      CFLKeyIdentity = true;
    }
    if (!cliErrors.empty()) {
      for (const auto &e : cliErrors)
        errs() << argv[0] << ": CLI sanity: " << e << "\n";
      return 1;
    }
  }


  if (int rc = kaApplyMemLimit())
    return rc;
  if (int rc = kaLoadModules(argv[0]))
    return rc;

  // Main workflow
  kaSelectFieldBuckets();
  GlobalCtx.constraintGraph.setFieldBuckets(CFLFieldBuckets);

  bool exitNow = false;
  if (int rc = kaIRCensusGate(exitNow); rc || exitNow)
    return rc;

  CallGraphPass CGPass(&GlobalCtx);
  auto tRun = std::chrono::steady_clock::now();
  CGPass.run(GlobalCtx.Modules);
  auto tRunEnd = std::chrono::steady_clock::now();
  Diag << "TIMER CGPass.run "
       << std::chrono::duration_cast<std::chrono::milliseconds>(tRunEnd - tRun).count()
       << " ms\n";

  if (!CallGraphJSON.empty()) {
    CGPass.dumpCallGraphJSON(CallGraphJSON);
  }
  if (!IRSidecarDir.empty()) {
    IRSidecarExporter Sidecar(&GlobalCtx);
    Sidecar.dump(IRSidecarDir);
  }

  return 0;
}
