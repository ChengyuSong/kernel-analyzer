/*
 * main function
 *
 * Copyright (C) 2012 Xi Wang, Haogang Chen, Nickolai Zeldovich
 * Copyright (C) 2015 Byoungyoung Lee
 * Copyright (C) 2016 Kangjie Lu
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/ManagedStatic.h>
#include <llvm/Support/PrettyStackTrace.h>
#include <llvm/Support/ToolOutputFile.h>
#include <llvm/Support/SystemUtils.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/Signals.h>
#include <llvm/Support/Path.h>

#include <chrono>
#include <memory>
#include <vector>
#include <sstream>
#include <fstream>
#include <new>
#include <sys/resource.h>
#include <unistd.h>

#include "Global.h"
#include "Pass.h"
#include "PointTo.h"
#include "CallGraph.h"
#include "Reachable.h"
#include "LLMClient.h"
#include "LLMAnalysis.h"
#include "IRSidecar.h"
#include "IRCensus.h"
#include <map>
#include <set>

using namespace llvm;

cl::list<std::string> InputFilenames(
  cl::Positional, cl::ZeroOrMore, cl::desc("<input bitcode files>"));

cl::opt<std::string> BCListFile(
  "bc-list", cl::desc("File containing input bitcode file paths, one per line"), cl::init(""));

cl::opt<unsigned> VerboseLevel(
  "verbose", cl::desc("Verbose level"), cl::init(0));

cl::opt<bool> CFLGlobalDedup(
  "cfl-global-dedup",
  cl::desc("Enable global union-find dedup with dense ID remapping for CFL edge construction"),
  cl::init(true));

cl::opt<bool> CFLLocalAllocaSummary(
  "cfl-local-alloca-summary",
  cl::desc("Enable non-escaping local alloca store/load summarization in CFL edge construction"),
  cl::init(true));

cl::opt<std::string> DumpBidMapping(
  "dump-bid-mapping", cl::desc("Dump basic block ID mapping, format: bid,fun_GUID,filepath:linenum"), cl::init(""));

cl::opt<std::string> DumpFuncInfo(
  "dump-func-info", cl::desc("Dump function info, format: fun_GUID,fun_name,filepath,start_linenum,end_linenum"), cl::init(""));

cl::opt<std::string> DumpAnnotatedIR(
  "dump-annotated-ir", cl::desc("Dump annotated IR"), cl::init(""));

cl::opt<std::string> GrammarFile(
  "grammar-file", cl::desc("Grammar file for CFL-reachability analysis"), cl::init(""));

cl::opt<std::string> CFLEdgeOutput(
  "cfl-edge-output", cl::desc("Output file for CFL-reachability edges"), cl::init(""));

cl::opt<std::string> VSnapshotOutput(
  "v-snapshot", cl::desc("Output file for compact CFL V-relation snapshot"), cl::init(""));

cl::opt<std::string> LLMServerHost(
  "llm-server-host", cl::desc("Hostname of local LLM server"), cl::init(""));

cl::opt<unsigned> LLMServerPort(
  "llm-server-port", cl::desc("Port of local LLM server"), cl::init(0));

cl::opt<std::string> InvokeProposalsFile(
  "invoke-proposals",
  cl::desc("Mine kerneldoc for INVOKE registration contracts (task #28 "
           "tier 3) and write REVIEW proposals to this file, then exit. "
           "Requires --kernel-src and an LLM server (--llm-server-host/"
           "-port), or --invoke-mine-dry to validate extraction offline. "
           "Proposals are never auto-applied"),
  cl::init(""));

cl::opt<std::string> KernelSrcTree(
  "kernel-src",
  cl::desc("Kernel source tree for kerneldoc extraction"),
  cl::init(""));

cl::opt<bool> InvokeMineDry(
  "invoke-mine-dry",
  cl::desc("Extract + prefilter kerneldoc candidates and record batch "
           "prompts without contacting the LLM"),
  cl::init(false));

cl::opt<bool> QueryLLM(
  "query-llm", cl::desc("Run LLM queries, save results to files, then exit"), cl::init(false));

cl::opt<std::string> AllocatorFile(
  "allocator-file", cl::desc("Path to allocator candidates JSON file (read or write)"), cl::init(""));

cl::opt<std::string> ContainerFile(
  "container-file", cl::desc("Path to container functions JSON file (read or write)"), cl::init(""));

cl::opt<std::string> CompressedGraphOutput(
  "cfl-compressed-output",
  cl::desc("Output compressed CFL constraint graph"),
  cl::init(""));

cl::list<std::string> CompressedGraphInputs(
  "cfl-compressed-input",
  cl::desc("Compressed graph files for compositional solving"));

cl::opt<bool> CFLCompositional(
  "cfl-compositional",
  cl::desc("Run per-TU CFL solving and compose compressed results (default on)"),
  cl::init(true));

cl::opt<bool> CFLPreSolveMerge(
  "cfl-presolve-merge",
  cl::desc("Solve the memory-free a/f sublanguage first and merge mutual-V' "
           "classes before the full CFL solve (default off)"),
  cl::init(false));

cl::opt<bool> CFLPreSolveOnce(
  "cfl-presolve-once",
  cl::desc("Run the pre-solve copy/field merge only on the INITIAL graph "
           "and skip it for wiring iterations >= 1 (flows-to from-scratch "
           "mode). Rationale (2026-08-16 decomposition): the re-run on the "
           "post-wiring graph is a one-time giant-SCC discovery costing "
           "56% of km fs41 wall; the in-drain a-SCC collapse discovers the "
           "same quotient (first sweep is pulled earlier when this is on). "
           "Answers are preserved either way: pre-solve merges are "
           "exactness-preserving, so withholding them changes speed, not "
           "the closure. A/B-gated before any default flip"),
  cl::init(false));

cl::opt<bool> CFLFptrSlice(
  "cfl-fptr-slice",
  cl::desc("Keep only constraint-graph components reachable from function "
           "pointers (callgraph-only slicing, default off)"),
  cl::init(false));

cl::opt<bool> CFLFlowsTo(
  "cfl-flows-to",
  cl::desc("Resolve icalls by answer-anchored root propagation instead of "
           "all-pairs CFL saturation (v0: field-insensitive, monolithic)"),
  cl::init(false));

cl::opt<bool> CFLFlowsToSlice(
  "cfl-flows-to-slice",
  cl::desc("Before flows-to propagation, prune to the derivation slice: "
           "1-bit function->fptr taint with Steensgaard-class memory "
           "jumps, closed under alias-evidence origins"),
  cl::init(false));

cl::opt<bool> CFLResidueCopies(
  "cfl-residue-copies",
  cl::desc("Encode unknown-layout memcpy and aggregate accesses as per-"
           "residue field copies instead of wildcard loops (flows-to "
           "only; precise for struct-copy idioms, costly on container-"
           "churn C++ — evaluate per target codebase)"),
  cl::init(false));

cl::opt<std::string> CFLTraceFunc(
  "cfl-trace-func",
  cl::desc("Trace flows-to fact propagation for the address-taken function "
           "whose name contains this substring: log every class its root "
           "reaches (capped) and the final reach set, to localize where a "
           "flow is lost"),
  cl::init(""));

cl::opt<std::string> CFLTraceFptr(
  "cfl-trace-fptr",
  cl::desc("After the flows-to fixpoint, dump a backward slice from the "
           "fptr class of icalls in functions whose name contains this "
           "substring, annotated with traced-root presence, to localize "
           "where a flow is severed"),
  cl::init(""));

cl::opt<std::string> CFLTraceValue(
  "cfl-trace-value",
  cl::desc("At the flows-to fixpoint, dump class/facts/cells for every "
           "pointer value in functions whose name contains this substring"),
  cl::init(""));

cl::opt<bool> CFLCoTravelStats(
  "cfl-cotravel-stats",
  cl::desc("After the flows-to fixpoint, report root co-travel statistics: "
           "roots with identical (class, shift) incidence columns are "
           "bundleable into one plane bit — the ratio bounds the root-"
           "bundling win (native R planes only, bridged RB excluded)"),
  cl::init(false));

cl::opt<unsigned> CFLFlowsToMaxIters(
  "cfl-flows-to-max-iters",
  cl::desc("Cap on flows-to outer fixpoint iterations (resolve icalls -> "
           "wire callee arg/ret flows -> re-solve). Hitting the cap with "
           "unprocessed wirings is reported as an UNSOUND-RISK warning"),
  cl::init(10));

cl::opt<bool> CFLPrintfVarargSink(
  "cfl-printf-vararg-sink",
  cl::desc("Skip vararg-summary wiring at variadic callsites whose constant "
           "format string (last fixed param, __printf convention) proves the "
           "varargs are read-only renderer inputs: no capture, no dispatch, "
           "no %pV forwarding, no %n. Non-constant or non-benign formats "
           "keep full wiring"),
  cl::init(true));

cl::opt<bool> CFLVerifyClosure(
  "cfl-verify-closure",
  cl::desc("After the flows-to fixpoint, run one full non-delta scan of all "
           "propagation/join/bridge rules and assert none still fires — a "
           "per-run certificate of the closure property the delta/backlog "
           "machinery is supposed to maintain (the Lean SolverModel "
           "assumption)"),
  cl::init(false));

cl::opt<bool> CFLSolverProfile(
  "cfl-solver-profile",
  cl::desc("rdtsc phase accounting inside the flows-to pop loop (join / "
           "bridge / scan / wflag / a-prop / f-prop) to locate the time "
           "sink before optimizing"),
  cl::init(false));

cl::opt<bool> LogTimestamps(
  "log-timestamps",
  cl::desc("Prefix every KA_LOG line with [+<seconds>] elapsed since "
           "process start (phase profiling; default off — the prefix "
           "changes the log format pin-extraction scripts anchor on)"),
  cl::init(false));

cl::opt<unsigned> CFLFieldBuckets(
  "cfl-field-buckets",
  cl::desc("Number of bucketed field-offset labels for field-sensitive CFL "
           "memory modeling (0 = field-insensitive, default)"),
  cl::init(0));

cl::opt<bool> IRCensusOpt(
  "ir-census",
  cl::desc("Enumerate every IR construct kind in the corpus, classify "
           "each against the edge builder's disposition table (handled / "
           "justified no-op / suspect / undispositioned), print the "
           "census, then exit — the encoder totality audit"),
  cl::init(false));

cl::opt<bool> IRCensusStrict(
  "ir-census-strict",
  cl::desc("Closed-world enforcement: run the census and ABORT if any "
           "construct kind in the corpus lacks a disposition. With "
           "--ir-census: audit-and-exit (exit 1 on violation). Alone: "
           "gate — census summary runs before the analysis and a "
           "violation kills the run instead of silently dropping edges"),
  cl::init(false));

cl::opt<std::string> IRCensusOut(
  "ir-census-out",
  cl::desc("Write the full census as JSON to this path: dispositions, "
           "intrinsics, constexprs, ALL external callees, the classified "
           "inline-asm table, and the unsoundness ledger (implies "
           "running the census)"),
  cl::init(""));

cl::opt<bool> CFLStaticCall(
  "cfl-static-call",
  cl::desc("Model kernel static_call: direct calls to undefined "
           "__SCT__X trampolines dispatch through __SCK__X's func "
           "slot (initializer + in-corpus __static_call_update stores "
           "are already IR-visible); the callsite becomes an icall "
           "resolved by flows-to. Off = trampoline stays an opaque "
           "extern call (pre-#14 boundary assumption)"),
  cl::init(true));

cl::opt<bool> CFLLinkerArrays(
  "cfl-linker-arrays",
  cl::desc("Model linker-materialized pointer arrays: alias each "
           "undefined __start_X/__stop_X extern global to the union of "
           "section-X members (IR globals with that section attribute "
           "plus module-asm PREL32 entry targets), and treat module-asm-"
           "referenced functions as address-taken. Kernel initcalls / "
           "__param / pci_fixup / ftrace_events / setup / bpf_raw_tp. "
           "Off = those loads resolve to nothing (pre-#22 behavior)"),
  cl::init(true));

cl::opt<bool> CFLBidiPrune(
  "cfl-bidi-prune",
  cl::desc("Before the flows-to solve, compute the field-matched "
           "bidirected partition (union-find with label-collision "
           "unification, O(m a(n))) and PRUNE origin roots whose "
           "partition's d/f cone never touches an fptr partition "
           "(pruned set recorded; cone oracle re-admits at wiring — "
           "#43 fix b82985d). Part of the canonical kernel config. "
           "Answer-preserving at FI; under fs it is strictly TIGHTER "
           "(pruned origins also stop feeding smear-producing cluster "
           "merges) — flag-match pins when comparing"),
  cl::init(false));

cl::opt<bool> CFLLazyMint(
  "cfl-lazy-mint",
  cl::desc("Demand-driven flows-to roots: mint only origin/identity roots "
           "backward-reachable from an fptr class (a/f flow edges plus "
           "cell->owner hops), re-expanding at every drain fixpoint as "
           "merges coarsen the quotient. Function roots (the answer "
           "alphabet) are always minted. Answers must be IDENTICAL to "
           "the full mint; only the propagated fact mass shrinks"),
  cl::init(false));

cl::opt<bool> CFLProbeRodataJoins(
  "cfl-probe-rodata-joins",
  cl::desc("MEASUREMENT-ONLY UNSOUND PROBE: skip cluster joins keyed by "
           "witness classes containing a constant (rodata) global — "
           "upper-bounds the closure-size win of the copy-not-unify "
           "refinement (task #25). Over-removes const-table read paths; "
           "answers WILL drop. Do not combine with --cfl-verify-closure"),
  cl::init(false));

cl::opt<bool> CFLCensusInvoke(
  "cfl-census-invoke",
  cl::desc("MEASUREMENT-ONLY census: scan defined functions for the "
           "(fn,data) registration shapes behind the INVOKE summary atom "
           "(fptr formal invoked with another formal; formal stored into "
           "another formal's field; formals co-stored into one object), "
           "then rank candidates by constant-Function evidence at their "
           "direct callsites. Emits proposal lines for review; adds no "
           "edges"),
  cl::init(false));

cl::opt<bool> CFLCensusFields(
  "cfl-census-fields",
  cl::desc("MEASUREMENT-ONLY census of family-2/3 store-side "
           "registration channels: (struct,offset) field keys with "
           "constant-Function stores on the registration side and "
           "field-load-fed icalls on the dispatch side, with paired "
           "sibling-store and ops-struct tallies (task #29). Adds no "
           "edges"),
  cl::init(false));

cl::opt<bool> CFLRegFieldReport(
  "cfl-regfield-report",
  cl::desc("Post-solve targeted-fs detector: rank (struct+offset) "
           "registration fields by the gap between resolved icall "
           "fanout at their readers and the witnessed registration "
           "population stored through them (constant stores, one "
           "install-API argument hop, initializer slots, copy-edge "
           "closure). Narrow population under wide fanout = the "
           "deep-collapse signature; emits a suggested "
           "--cfl-nexus-fields list. Report only, adds no edges"),
  cl::init(false));

cl::opt<bool> CFLRegFieldApply(
  "cfl-regfield-apply",
  cl::desc("Auto-generated identity channels from the regfield "
           "detector: for keys whose registration population is "
           "machine-certified CLOSED (every mutation path classified; "
           "zero unwitnessed stores, atomics, bulk copies, or "
           "escaping slot addresses), intersect resolution at the "
           "key's reader sites with the witnessed table — monotone "
           "-N/+0 removal, certified per key in the RegFieldChannel "
           "ledger. OPEN keys are never touched (they stay report "
           "material for the manual channel pipeline)"),
  cl::init(false));

cl::opt<bool> CFLIterCapOk(
  "cfl-iter-cap-ok",
  cl::desc("Accept UNSOUND capped output when the flows-to outer "
           "fixpoint hits --cfl-flows-to-max-iters before converging. "
           "Default: refuse and exit(1) — a silently capped result is "
           "a missing-flow answer set"),
  cl::init(false));

cl::opt<bool> CFLRegFieldAudit(
  "cfl-regfield-audit",
  cl::desc("With --cfl-regfield-apply: emit a provenance certificate "
           "for every applied key — per-source table breakdown "
           "(const-initializer / store / install-hop / copy-closure) "
           "+ risk class (GREEN rodata-structural, YELLOW "
           "hazard-counter-dependent, ORANGE copy-closure-dependent) "
           "+ the full table, for the channel audit"),
  cl::init(false));

cl::opt<std::string> CFLProbeStratumAblate(
  "cfl-probe-stratum-ablate",
  cl::desc("MEASUREMENT-ONLY UNSOUND probe (task #32): non-empty value "
           "severs inttoptr bridges classified as phys-stratum "
           "(directmap/vmemmap/kernelmap/mm-fn) — the result becomes an "
           "opaque identity root. Measures blob fragmentation and the "
           "answer delta of stratum separation. NEVER a shipped config"),
  cl::init(""));

cl::opt<bool> CFLProbeUserCopyAblate(
  "cfl-probe-usercopy-ablate",
  cl::desc("MEASUREMENT-ONLY UNSOUND probe (task #32): sever the memory "
           "edges introduced by the from-user copy primitives "
           "(_copy_from_user et al.) — the uaccess `~{memory}`-clobber "
           "asm raw-ptr closure that carries user bytes into the "
           "destination buffer. Tests whether user-copied memory affects "
           "the indirect-call graph (expect -0/+0). NEVER a shipped config"),
  cl::init(false));

cl::opt<bool> CFLCertUserCopy(
  "cfl-cert-usercopy",
  cl::desc("MEASUREMENT-ONLY certificate (task #32): tag the from-user "
           "memory ingress sites (the same copy-body + __get_user asm "
           "closures the ablation probe severs) with synthetic origin "
           "roots and report which indirect-call operands their bytes "
           "reach in the flows-to closure — the positive-direction "
           "crossing inventory (expect empty modulo certified crossings). "
           "Adds measurement roots; answers may smear — never compare "
           "its answer set against pins"),
  cl::init(false));

cl::opt<bool> CFLConfirmSinks(
  "cfl-confirm-sinks",
  cl::desc("MEASUREMENT-ONLY confirmer (task #32): machine-check the "
           "trace-payload read-back contract — walk every payload "
           "accessor callsite (ring_buffer_event_data, "
           "perf_trace_buf_alloc) and verify no value loaded back out "
           "of a payload cell feeds an indirect call. Reports "
           "CONFIRMED/ESCAPE/VIOLATION per site; adds no edges"),
  cl::init(false));

cl::opt<bool> CFLSinkInstr(
  "cfl-sink-instr",
  cl::desc("Reviewed sink model (task #31/#32 design): seal cluster "
           "joins at trace-payload cells (ring_buffer_/trace_buf "
           "family) — stores keep their own cell, joins to stored "
           "objects' keys are suppressed. Auto-runs the read-back "
           "contract confirmer and REFUSES to run on any VIOLATION; "
           "ESCAPE sites are inventoried for the documented review"),
  cl::init(false));

cl::opt<bool> CFLCensusPtrToInt(
  "cfl-census-ptrtoint",
  cl::desc("MEASUREMENT-ONLY census (task #33): classify every ptrtoint "
           "by its forward use-chains (escape > other > variable-arith > "
           "mask > const-add-chain-to-inttoptr > compare-only) — sizes "
           "the int-provenance residue design: const chains are GEPs in "
           "disguise (residue-encodable, wildcard-suppressible), "
           "cmp-only sites need no wildcard at all. Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLCensusTypeRej(
  "cfl-census-type-rej",
  cl::desc("MEASUREMENT-ONLY reverse census of the type filter: per "
           "icall, CFL-derived fn candidates vs after isCompatible, "
           "rejected pairs bucketed by the first failing check (argc / "
           "ret / param kind); crossed with acceptance elsewhere — a "
           "function derived somewhere but type-rejected at every "
           "deriving site is the candidate missing-target inventory "
           "(cf. the certified static_call +29). Changes no answers"),
  cl::init(false));

cl::opt<std::string> CFLGTTypeCensus(
  "cfl-gt-type-census",
  cl::desc("MEASUREMENT-ONLY ground-truth type census: file of "
           "'frame1;frame2;... target' lines (dynamically observed "
           "caller-chain -> callee). For each record, test isCompatible "
           "between the target and every indirect callsite in every "
           "recorded frame function; a record where sites exist but "
           "NONE accepts the target is a WITNESSED type-filter "
           "unsoundness (a runtime-true pair our type rules reject). "
           "Runs after module init, then exits — no solve"),
  cl::init(""));

cl::opt<bool> CFLFieldBucketsAuto(
  "cfl-field-buckets-auto",
  cl::desc("Pick the residue modulus P from the loaded corpus: census "
           "the fn-ptr slot offsets (same walk as "
           "--cfl-dump-fnptr-offsets) and choose the smallest prime "
           "whose same-struct collision residual is within "
           "--cfl-auto-buckets-residual-bp, capped by "
           "--cfl-auto-buckets-max. Explicit --cfl-field-buckets wins"),
  cl::init(false));

cl::opt<unsigned> CFLAutoBucketsResidualBP(
  "cfl-auto-buckets-residual-bp",
  cl::desc("Auto bucket selection: max tolerated same-struct colliding "
           "offset pairs, in basis points of all same-struct pairs "
           "(10 = 0.10%)"),
  cl::init(10));

cl::opt<unsigned> CFLAutoBucketsMax(
  "cfl-auto-buckets-max",
  cl::desc("Auto bucket selection: largest P considered (memory scales "
           "~linearly with P). If the residual target needs a larger P, "
           "the cap is taken and the shortfall is reported LOUDLY"),
  cl::init(127));

cl::opt<bool> CFLDumpFnptrOffsets(
  "cfl-dump-fnptr-offsets",
  cl::desc("MEASUREMENT-ONLY: dump every (struct, byte-offset) slot that "
           "holds a FUNCTION — from global initializers (ops tables) and "
           "direct fn-constant stores — as FNPTR-OFFSET lines, then exit. "
           "Input to the residue-modulus (Z_P) collision scorer: P must "
           "separate same-struct fn-ptr offsets or fs cannot split them"),
  cl::init(false));

cl::opt<bool> CFLCensusExternBound(
  "cfl-census-extern-bound",
  cl::desc("MEASUREMENT-ONLY census (task #45): rank called-but-never-"
           "defined functions (asm-defined symbols, firmware stubs) by "
           "pointer args / fn-ptr args / pointer returns — the summary-"
           "writing worklist for the extern boundary; sum=1 marks names "
           "the --func-summaries file already covers. Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLCensusTracepoint(
  "cfl-census-tracepoint",
  cl::desc("MEASUREMENT-ONLY census (task #35): size the tracepoint "
           "keyed-channel design. Classifies every "
           "tracepoint_probe_register-family callsite by how the tp "
           "argument is named (CONST @__tracepoint_* global = directly "
           "keyable / LOAD = struct-mediated, needs initializer pair "
           "correlation / FORMAL = in-family wrapper / OTHER), and "
           "checks every __traceiter_* body names its key global at "
           "the funcs-head load. Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLTracepointKeys(
  "cfl-tracepoint-keys",
  cl::desc("ADOPTED MODEL (task #35, default ON; =false to opt out): "
           "per-tracepoint keyed probe "
           "channels. Every tracepoint_probe_register-family callsite "
           "is severed from the generic body (whose shared tp formal "
           "is the channel that pools ALL tracepoints' probes into "
           "every __traceiter_* dispatch); CONST-key sites bind "
           "probe/data to the key global's channel cells directly, and "
           "the two struct-mediated registrars (trace_event_reg, "
           "bpf_probe_register) are covered by walking the "
           "trace_event_call / bpf_raw_event_map static initializers "
           "for (tp, probe) pairs. __traceiter_* icalls read their own "
           "key's channel. Unclassifiable sites keep generic wiring "
           "and are counted LOUDLY (census: zero at kernel scale)"),
  cl::init(true));

cl::opt<bool> CFLStaticOpsTables(
  "cfl-static-ops-tables",
  cl::desc("ADOPTED MODEL (task #36, default ON; =false to opt out): "
           "answer-level channel for "
           "static_call keys updated from ops-struct tables. At "
           "__static_call_update(key, ops->field) sites the IR names "
           "the struct type and field index; the binding inventory is "
           "the set of same-typed global initializers (vmx/svm "
           "kvm_x86_ops, intel/amd x86_pmu, apic drivers). __SCT__ "
           "dispatch sites whose key is tabled take their targets from "
           "the table instead of the (type-fallback) graph answer; "
           "non-conforming update args untable the key LOUDLY and its "
           "sites keep graph behavior. Requires --cfl-static-call"),
  cl::init(true));

cl::opt<bool> CFLRodataCopy(
  "cfl-rodata-copy",
  cl::desc("REVIEWED MODEL (task #25): copy-not-unify for rodata "
           "origins. Const globals are immutable, so their cells "
           "transmit contents to readers (initializer-planted facts "
           "still flow: const ops tables resolve) but never unify "
           "reader classes with each other — the string-literal / "
           "const-struct witness glue never forms. Reuses the #30 "
           "provenance-protection machinery: writer joins (initializer "
           "cells) merge, reader joins attach via non-transitive "
           "bridges, mixed cells demote soundly. km over-removal upper "
           "bound was -29,128/+0 (30%)"),
  cl::init(false));

cl::opt<bool> CFLCensusIcallShape(
  "cfl-census-icall-shape",
  cl::desc("MEASUREMENT-ONLY census (task #37): classify every fat "
           "answer site (>=100 targets) by the IR shape of its fptr "
           "chain (formal param / struct-field load / global load / "
           "phi-select) and by whether its operand class is the giant "
           "quotient class — names the families for the next "
           "answer-level campaigns"),
  cl::init(false));

cl::opt<bool> CFLProbeBornHub(
  "cfl-probe-born-hub",
  cl::desc("MEASUREMENT-ONLY probe (task #38): after the pre-solve "
           "mutual-V' merge, induce the forward-flow subgraph on the "
           "largest (born-giant) SCC and iteratively remove the "
           "highest-degree node, reporting the largest-SCC shatter "
           "curve — decides whether phase-1 hub cutting is viable"),
  cl::init(false));

cl::opt<bool> CFLPreSolveExact(
  "cfl-presolve-exact",
  cl::desc("EXPERIMENT (task #38): pre-solve merge quotients only raw "
           "mutual-flow SCCs (provable value equality) instead of "
           "V-alias-connectivity components (Steensgaard-style "
           "over-unification that manufactures the born giant). "
           "Precision can only improve; cost is the question"),
  cl::init(false));

cl::opt<bool> CFLPreSolveCone(
  "cfl-presolve-cone",
  cl::desc("ADOPTED (task #38, default ON; =false to opt out): keep the "
           "pre-solve V-component "
           "quotient for the data plane but exclude nodes in the "
           "backward value-flow cone of icall operands — exactness "
           "only where answers live, bounded class-count increase"),
  cl::init(true));

cl::opt<bool> CFLJoinCone(
  "cfl-join-cone",
  cl::desc("EXPERIMENT (task #38 rung 2): apply the answer-relevance "
           "discipline to IN-SOLVE cluster joins — every origin is "
           "protection-eligible, and pure-reader cells in the fptr "
           "backward cone attach via non-transitive copy-out bridges "
           "instead of merging (writers and non-cone readers merge as "
           "today). Requires --cfl-presolve-cone for the cone"),
  cl::init(false));

cl::opt<bool> CFLCensusCouplers(
  "cfl-census-couplers",
  cl::desc("MEASUREMENT-ONLY census (task #38, modularity thesis): "
           "track per-class subsystem masks over owned DATA origins "
           "(fn identities excluded) and record every cross-subsystem "
           "WELD at merge time, blamed by the shared join origin; "
           "report top welders + icall-operand data-subsystem "
           "diversity. Tests whether the kernel's object plane is "
           "naturally compartmentalized"),
  cl::init(false));

cl::opt<bool> CFLCensusNexus(
  "cfl-census-nexus",
  cl::desc("MEASUREMENT-ONLY census (task #38): discover nexus structs "
           "— rank named struct types by how many subsystems store "
           "POINTERS through GEPs into them (the FI-cell coupling "
           "carriers), with reader diversity alongside"),
  cl::init(false));

cl::opt<std::string> CFLNexusFields(
  "cfl-nexus-fields",
  cl::desc("Surgical field sensitivity (task #39): comma-separated named "
           "struct list (e.g. task_struct,file,cred) or 'default' (the "
           "fat-object census list). ONLY origins of these nexus types "
           "carry exact field residues; every other origin mints on the "
           "wildcard plane, which is bit-identical to FI for it (one "
           "(o,X) join cluster, no exact keys, no VX bridges) — the "
           "residue-plane cost is confined to the nexus population. "
           "Requires --cfl-field-buckets>0 (auto-set to 13 if unset)"),
  cl::init(""));

cl::opt<bool> CFLInternPlanes(
  "cfl-intern-planes",
  cl::desc("Share dense fact planes copy-on-write (task #46): a full-"
           "plane delta arriving at an empty plane is ADOPTED (O(1)) "
           "instead of copied, the share walks copy chains via full-"
           "plane pushes, and pointer-equality fast paths skip the "
           "copy+diff on re-offers. Byte-identical answers by "
           "construction (COW detach on first divergent write). Only "
           "effective in the sequential solver (T=1): at T>1 concurrent "
           "in-place OR-ins would race with COW pointer swaps"),
  cl::init(true));

cl::opt<bool> CFLJoinFastpath(
  "cfl-join-fastpath",
  cl::desc("Cluster-mark join fast path (task #48): skip the cluster-rep "
           "registry probe when the (cluster, origin, shift) join has "
           "already been performed — the cellJoined planes are a "
           "monotone mirror of join effects, so a hit is always safe to "
           "skip and a miss only falls through to the full probe. "
           "Byte-identical answers by construction; =false to ablate "
           "(perf measurement only)"),
  cl::init(true));

cl::opt<bool> CFLOriginBundles(
  "cfl-origin-bundles",
  cl::desc("Origin-equivalence bundles (docs/origin-bundles-design.md): "
           "at periodic drain checkpoints, exact partition refinement "
           "over full per-rid state (all plane families) finds origins "
           "that co-travel; each group is renumbered to ONE fact id and "
           "the rid space is compacted (the width lever). At drain end "
           "the planes are expanded back to the original rid space, so "
           "resolution, verification and instruments are unaffected. "
           "Exactness: bundle_exact + row_determined (proof/lean/"
           "Bundles.lean) + runtime L1 cluster-equality assertions. "
           "v1: mono only; refuses batch/bidi/incremental/probe combos. "
           "STATUS (Gate 2, 2026-08-15): EXACT at km scale (fs13 "
           "byte-identical through 2 epochs + expansion) but PARKED — "
           "epoch passes cost O(live mass) against short drains and "
           "the compression dies at expansion/rebuild (157m vs 32m at "
           "km fs13); see docs/origin-bundles-design.md post-mortem"),
  cl::init(false));

cl::opt<unsigned long long> CFLBundleEpochFacts(
  "cfl-bundle-epoch-facts",
  cl::desc("Fact-mass threshold for the first bundle epoch (with "
           "--cfl-origin-bundles); each next attempt waits for 2x the "
           "mass at the last attempt. Mass-based, not pop-based: "
           "co-travel forms as the hub saturates (late in the drain), "
           "and a refinement pass costs one stream over live mass, so "
           "doubling bounds total epoch cost at ~2 final-mass passes "
           "while landing the effective epochs where the merge "
           "re-offer traffic is"),
  cl::init(1ull << 27));

cl::opt<bool> CFLBundleProbe(
  "cfl-bundle-probe",
  cl::desc("Post-solve probe for stage-2 root bundling (task #47): "
           "group roots that co-travel BY CONSTRUCTION (co-resident "
           "minted classes; identical successor signatures), then "
           "classify every (plane,group) as FULL (bundleable; savings "
           "= members-1) or PARTIAL (design-1 split events / design-2 "
           "exactness violations). Decision data only; no behavior "
           "change"),
  cl::init(false));

cl::opt<bool> CFLInternSweep(
  "cfl-intern-sweep",
  cl::desc("Additionally run a periodic content-hash sweep unifying "
           "already-materialized duplicate R/joined planes (requires "
           "--cfl-intern-planes). Measured 2026-08-07: finds ~9% of "
           "planes mid-drain but yields no fast-path hits and no RSS "
           "high-water change (temporal divergence — duplication is an "
           "end-state property), costs ~11% at library scale. Kept as "
           "an instrument"),
  cl::init(false));

cl::opt<unsigned> CFLBatchRoots(
  "cfl-batch-roots",
  cl::desc("Origin-batched flows-to solving (task #40): mint and drain "
           "roots K at a time, releasing all fact planes between "
           "batches; only the union-find quotient, join keys, bridges "
           "and harvested answer bits persist. Outer rounds repeat "
           "until a full pass adds no merges (same closure, monotone-"
           "merge argument). Memory = graph + one batch's planes. "
           "0 = off (monolithic). Diagnostics that read live planes "
           "post-solve see only the last batch"),
  cl::init(0));

cl::opt<unsigned> CFLBatchWorkers(
  "cfl-batch-workers",
  cl::desc("Process-parallel batches (task #41, requires "
           "--cfl-batch-roots): fork P workers after graph build — the "
           "graph and quotient are shared copy-on-write, so memory = "
           "graph + P live batch plane-sets. Workers drain single-"
           "threaded and stream effectual events (key inserts, merges) "
           "+ harvested answer bits through /tmp scratch files; the "
           "parent replays them (Jacobi rounds, same closure). Size P "
           "by what fits: peak ~ graph + P * (plane total / #batches). "
           "0/1 = sequential batches"),
  cl::init(0));

cl::opt<std::string> CFLBatchSpill(
  "cfl-batch-spill",
  cl::desc("Plane spill/restore for batched solving (task #42, requires "
           "--cfl-batch-roots): serialize each batch's fact planes to "
           "this directory after its drain; later rounds RESTORE and "
           "drain only the cross-batch delta (classes touched by merges/"
           "bridges since the save) instead of re-deriving from seeds — "
           "offload over recompute. Point it at a filesystem with space "
           "(NOT tmpfs; spill ~ total fact mass as u32 lists, and a "
           "docker volume works). Empty = recompute mode"),
  cl::init(""));

cl::opt<bool> CFLCensusStrata(
  "cfl-census-strata",
  cl::desc("MEASUREMENT-ONLY census (task #32): classify every "
           "inttoptr/ptrtoint by its int computation (page_offset_base/"
           "vmemmap_base/phys_base loads, direct-map constants, mm/trace "
           "function context) + census user-copy boundary interfaces — "
           "the stratum-crossing site inventory for the separation "
           "theorem. Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLProbeBlobFormation(
  "cfl-probe-blob-formation",
  cl::desc("MEASUREMENT-ONLY probe (task #31): log merge events while "
           "both classes are still small/nameable (min side >= 64 or "
           "size milestones), tagged by channel (join key origin, "
           "a-scc, protection paths). Report reconstructs the final "
           "giant class's growth history — causal channels instead of "
           "member names. Adds no edges"),
  cl::init(false));

cl::opt<std::string> CFLProbeSinkAblate(
  "cfl-probe-sink-ablate",
  cl::desc("MEASUREMENT-ONLY UNSOUND probe: comma-separated name "
           "substrings; cells whose class belongs to a matching "
           "function/global are treated as write-only sinks (all "
           "cluster joins skipped). Quantifies an instrumentation "
           "channel's contribution to cell fusion, fact mass and "
           "answers (task #30 follow-on). NEVER a shipped config"),
  cl::init(""));

cl::opt<bool> CFLProposeOpsSt(
  "cfl-propose-ops-st",
  cl::desc("PROPOSE (never auto-apply) ST/ALIAS transfer summaries for "
           "registration-setter helpers discovered by the ops-pairs "
           "call-escape walk: a helper qualifies only if EVERY "
           "instruction is replicable per callsite (formal-base stores "
           "of formal/null/scalar values, non-pointer reads, no "
           "formal-derived call operands). Output is reviewable "
           "func_summaries.txt syntax (task #30 store-side splitting)"),
  cl::init(false));

cl::opt<bool> CFLOpsPairs(
  "cfl-ops-pairs",
  cl::desc("Certify (ops-global, container) pair invariants from IR use "
           "evidence (every use of a const fn-table global classified: "
           "field store -> container captured; initializer embedding -> "
           "parent global; else INCOMPLETE -> pooled) and, in step 2, "
           "tighten certified member fns' receiver formals to their "
           "paired containers (task #30). Certificates are derived, "
           "never assumed; violations stay pooled + LEDGERed"),
  cl::init(false));

cl::opt<bool> CFLProbeOpsMono(
  "cfl-probe-ops-mono",
  cl::desc("MEASUREMENT-ONLY probe (task #30): classify each two-level "
           "dispatch site (obj->ops->fn) by whether its resolved targets "
           "lie inside a single ops-global member set — derives the "
           "kernel-modularity invariant from the sound analysis (mono "
           "sites certify per-ops pairing; polymorphic sites form the "
           "violation/imprecision ledger). Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLProbeOriginSplit(
  "cfl-probe-origin-split",
  cl::desc("MEASUREMENT-ONLY probe (task #29): at each flows-to "
           "resolution round, compare the pooled icall answer against "
           "the counterfactual origin-indexed answer (targets present "
           "in the merged cluster classes of the container origins the "
           "fptr was loaded from) and report cluster diversity — sizes "
           "the same-origin binding lever and how much of it needs "
           "witness-based unmerging. Adds no edges, changes no answers"),
  cl::init(false));

cl::opt<bool> CFLConfirmInvoke(
  "cfl-confirm-invoke",
  cl::desc("Auto-confirm INVOKE pair summaries where the proof is local "
           "(task #28 tier 2): DIRECT synchronous invocation of a fn "
           "formal, and PASSTHRU forwarding into already-summarized "
           "INVOKE callees (wrapper-chain fixpoint) — both under the "
           "completeness discipline (every pointer formal accounted or "
           "reject to LEDGER). Deferred FIELD/COSTORE shapes stay "
           "census-reported for human review"),
  cl::init(false));

cl::opt<bool> CFLConfirmFresh(
  "cfl-confirm-fresh",
  cl::desc("Body-confirm PURE-FRESH allocation wrappers (returns trace "
           "only to fresh sources, no escapes, no pointer side effects) "
           "and promote them to allocator status, to fixpoint over "
           "wrapper chains — per-callsite object identities for their "
           "callers (task #17). Rejections tallied by reason"),
  cl::init(false));

cl::opt<std::string> CFLAblateMints(
  "cfl-ablate-mints",
  cl::desc("MEASUREMENT-ONLY UNSOUND PROBE: comma-separated names; skip "
           "minting identity roots whose canonical value is the named "
           "global or an instruction inside the named function. Separates "
           "hub-seeding witnesses from hub-riding ones (task #25)"),
  cl::init(""));

cl::opt<std::string> FuncSummaryFile(
  "func-summaries",
  cl::desc("Transfer-summary file (atoms: FRESH/CPY/ALIAS/ST/LD/NONE, "
           "ordered, first-match-wins, trailing '*' = prefix). When set, "
           "it is AUTHORITATIVE: replaces the hardcoded isAllocFn "
           "allocator table and adds copy/alias/container semantics at "
           "summarized callsites. See func_summaries.txt"),
  cl::init(""));

cl::opt<std::string> CFLAblateFuncs(
  "cfl-ablate-funcs",
  cl::desc("MEASUREMENT-ONLY UNSOUND PROBE: comma-separated function "
           "names whose bodies emit no edges (treated as opaque), to "
           "causally attribute hub-class gluing in the conflation "
           "report. Every ablation is WARNED loudly"),
  cl::init(""));

cl::opt<bool> CFLConflationReport(
  "cfl-conflation-report",
  cl::desc("After the flows-to fixpoint, rank functions as summary/clone "
           "candidates: shared-formal conflation (callers x facts in a "
           "pointer-formal's class) and allocation-site identity spread "
           "(classes carrying an internal alloc root x wrapper callers). "
           "The input queue for the offline proposer+confirmer loop"),
  cl::init(false));

cl::opt<bool> CFLRootRelevance(
  "cfl-root-relevance",
  cl::desc("After the flows-to fixpoint, measure the answer-relevant root "
           "fraction: function roots read at icall planes plus roots whose "
           "cluster key triggered a merge whose class lies on a backward "
           "path from some fptr class. Sizes the demand-driven-roots "
           "lever (solver work ~ |E| x |roots|)"),
  cl::init(false));

cl::opt<bool> CFLFlowsToIncremental(
  "cfl-flows-to-incremental",
  cl::desc("Continue the flows-to solve across resolution iterations "
           "instead of re-solving from scratch. Task #43 (b82985d) "
           "fixed the stale-bidi-cone divergence; km-validated EXACT "
           "for FI configs (byte-identical, faster) and AUTO-ENABLED "
           "there. Refused under field sensitivity (known pool-smear "
           "divergence) and unvalidated with batching/lazy-mint (not "
           "auto-enabled)"),
  cl::init(false));

cl::opt<unsigned> CFLSolverThreads(
  "cfl-solver-threads",
  cl::desc("Worker threads for the flows-to solver's bulk-synchronous "
           "wave phases (1 = sequential, 0 = hardware concurrency)"),
  cl::init(1));

cl::opt<unsigned> CFLSolverBlock(
  "cfl-solver-block",
  cl::desc("Classes per rank-ordered block within a solver wave; smaller "
           "blocks keep more within-wave downhill forwarding, larger "
           "blocks expose more parallelism"),
  cl::init(8192));

cl::opt<bool> CFLCGCacheStrict(
  "cfl-cache-strict",
  cl::desc("Strict compositional cache validation (coverage/freshness/compatibility)"),
  cl::init(true));

cl::opt<bool> CFLCGCacheRepair(
  "cfl-cache-repair",
  cl::desc("Repair compositional cache by recomputing missing/stale/incompatible modules"),
  cl::init(false));

cl::opt<bool> CFLCGAllowDuplicateCoverage(
  "cfl-cache-allow-duplicate-coverage",
  cl::desc("Allow multiple input .cflcg files to claim the same covered module"),
  cl::init(false));

cl::opt<std::string> CallGraphJSON(
  "callgraph-json", cl::desc("Export call graph to JSON file"), cl::init(""));

cl::opt<bool> CFLDumpCalleeMismatch(
  "cfl-dump-callee-mismatch",
  cl::desc("Per-callsite WARNING for callees found by type but not by CFL "
           "(can produce GBs of log on large inputs)"),
  cl::init(false));

cl::opt<bool> CFLDumpICalls(
  "cfl-dump-icalls",
  cl::desc("Dump one ICALL line per resolved (callsite, callee) pair; sort "
           "the lines to diff runs (5M+ lines on whole-kernel inputs)"),
  cl::init(false));

cl::opt<std::string> IRSidecarDir(
  "ir-sidecar-dir",
  cl::desc("Directory to write per-bc IR fact sidecar JSON files (<bc>.facts.json)"),
  cl::init(""));

cl::opt<int> MemLimitPct(
  "mem-limit", cl::desc("Memory limit as percentage of physical RAM (0 = unlimited, default 80)"), cl::init(80));

cl::opt<std::string> MemLimitMode(
  "mem-limit-mode",
  cl::desc("How --mem-limit is enforced: 'rss' (default) = watchdog "
           "thread on /proc/self/status VmRSS — measures RESIDENT "
           "memory, immune to allocator reservations / transient "
           "doublings / mapped files that inflate virtual size; 'as' = "
           "legacy RLIMIT_AS on virtual address space (overcounts by "
           "1.2-2x under many threads); 'off' = no in-process limit — "
           "use when a cgroup enforces it (docker --memory)"),
  cl::init("rss"));

// RSS watchdog (mem-limit-mode=rss): polls resident size and fails
// loud before the kernel OOM-killer picks a victim. Forked batch
// workers lose the parent's thread — they re-arm via this hook.
uint64_t KAMemLimitRssBytes = 0;
void kaStartRssWatchdog() {
  if (KAMemLimitRssBytes == 0)
    return;
  std::thread([] {
    for (;;) {
      std::this_thread::sleep_for(std::chrono::seconds(2));
      std::ifstream st("/proc/self/status");
      std::string line;
      while (std::getline(st, line)) {
        if (line.rfind("VmRSS:", 0) != 0)
          continue;
        const uint64_t kb = std::stoull(line.substr(6));
        if (kb * 1024ull > KAMemLimitRssBytes) {
          errs() << "ERROR: Out of memory: VmRSS " << (kb >> 20)
                 << " GB exceeded the " << (KAMemLimitRssBytes >> 30)
                 << " GB limit. Increase --mem-limit, use "
                    "--mem-limit-mode=off under a cgroup, or reduce "
                    "input/batch size.\n";
          _exit(1);
        }
        break;
      }
    }
  }).detach();
}

GlobalContext GlobalCtx;

#define Diag llvm::errs()

void IterativeModulePass::run(ModuleList &modules) {

  ModuleList::iterator i, e;
  Diag << "[" << ID << "] Initializing " << modules.size() << " modules\n";
  bool again = true;
  Iteration = 0;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      again |= doInitialization(i->first);
      // Diag << ".";
    }
    Iteration++;
  }
  Diag << "\n";

  unsigned changed = 1;
  while (changed) {
    changed = 0;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      Diag << "[" << ID << " / " << Iteration << "] ";
      // FIXME: Seems the module name is incorrect, and perhaps it's a bug.
      Diag << "[" << i->second << "]\n";

      bool ret = doModulePass(i->first);
      if (ret) {
        ++changed;
        Diag << "\t [CHANGED]\n";
      } else
        Diag << "\n";
    }
    Diag << "[" << ID << "] Updated in " << changed << " modules.\n";
    Iteration++;
  }

  Diag << "[" << ID << "] Postprocessing ...\n";
  again = true;
  Iteration = 0;
  while (again) {
    again = false;
    for (i = modules.begin(), e = modules.end(); i != e; ++i) {
      // TODO: Dump the results.
      again |= doFinalization(i->first);
    }
    Iteration++;
  }

  Diag << "[" << ID << "] Done!\n\n";
}

void doBasicInitialization(Module *M) {
  // struct analysis
  GlobalCtx.structAnalyzer.run(M, &(M->getDataLayout()));

  // collect global object definitions
  for (GlobalVariable &GV : M->globals()) {
    auto GVID = GV.getGUID();
    if (GV.hasExternalLinkage() || GV.hasExternalWeakLinkage()) {
      if (!GV.isDeclaration()) {
        assert(GV.hasInitializer());
        if (GlobalCtx.Gobjs.count(GVID) != 0) {
          // check for weak linkage
          if (GV.hasWeakLinkage()) {
            // keep the previous definition, even if it's weak too
            continue;
          } else if (!GlobalCtx.Gobjs[GVID]->hasWeakLinkage()) {
            // both are not weak
            WARNING("Global variable " << GV.getName()
                << " has been defined multiple times, previously in "
                << GlobalCtx.Gobjs[GVID]->getParent()->getModuleIdentifier()
                << ", and now in " << M->getModuleIdentifier() << "\n");
            continue;
          } // else fall through to replace weak definition
        }
        GlobalCtx.Gobjs[GVID] = &GV;
      } else {
        GlobalCtx.ExtGobjs[GVID] = &GV;
      }
    } else if (GV.hasInitializer()) {
      GlobalCtx.Gobjs[GVID] = &GV;
    }
  }

  // collect global function definitions
  for (Function &F : *M) {
    // Accept external, linkonce_odr, and weak_odr linkage.
    // C++ constructors/destructors often have linkonce_odr or weak_odr
    // linkage (e.g., inline definitions, template instantiations).
    if (!F.hasLocalLinkage()) {
      auto FID = F.getGUID();
      if (!F.isDeclaration() && !F.empty()) {
        if (GlobalCtx.Funcs.count(FID) != 0) {
          // check for weak/linkonce linkage
          if (F.isWeakForLinker()) {
            // keep the previous definition
            continue;
          } else if (!GlobalCtx.Funcs[FID]->isWeakForLinker()) {
            // both are strong definitions
            WARNING("Function " << F.getName()
                << " has been defined multiple times, previously in "
                << GlobalCtx.Funcs[FID]->getParent()->getModuleIdentifier()
                << ", and now in " << M->getModuleIdentifier() << "\n");
            continue;
          } // else fall through to replace weak/linkonce definition
        }
        GlobalCtx.Funcs[FID] = &F;
      } else {
        GlobalCtx.ExtFuncs[FID] = &F;
      }
    }
  }

  // Resolve global aliases (e.g., Itanium ABI C1->C2 constructor aliases)
  for (GlobalAlias &GA : M->aliases()) {
    if (GA.hasLocalLinkage())
      continue;
    auto *Aliasee = dyn_cast<Function>(GA.getAliasee()->stripPointerCasts());
    if (!Aliasee || Aliasee->isDeclaration() || Aliasee->empty())
      continue;
    auto AliasID = GA.getGUID();
    if (GlobalCtx.Funcs.count(AliasID) == 0)
      GlobalCtx.Funcs[AliasID] = Aliasee;
    // also remove from ExtFuncs if present
    GlobalCtx.ExtFuncs.erase(AliasID);
  }
}

int main(int argc, char **argv) {
  kaElapsedSec(); // anchor the --log-timestamps clock at process start

#ifdef SET_STACK_SIZE
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0) {
    rl.rlim_cur = SET_STACK_SIZE;
    setrlimit(RLIMIT_STACK, &rl);
  }
#endif

  // Print a stack trace if we signal out.
#if LLVM_VERSION_MAJOR == 3 && LLVM_VERSION_MINOR < 9
  sys::PrintStackTraceOnErrorSignal();
#else
  sys::PrintStackTraceOnErrorSignal(argv[0]);
#endif
  PrettyStackTraceProgram X(argc, argv);

  llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

  cl::ParseCommandLineOptions(argc, argv, "global analysis\n");

  if (!BCListFile.empty()) {
    std::ifstream ListFile(BCListFile);
    if (!ListFile.is_open()) {
      errs() << argv[0] << ": error opening bc-list file '" << BCListFile << "'\n";
      return 1;
    }
    std::string Line;
    while (std::getline(ListFile, Line)) {
      if (!Line.empty())
        InputFilenames.push_back(Line);
    }
  }

  if (InputFilenames.empty()) {
    errs() << argv[0] << ": no input files specified (use positional args or --bc-list)\n";
    return 1;
  }

  // CLI mode sanity: reject combinations where a requested feature would
  // be SILENTLY ignored by the selected solver mode. A misconfigured
  // whole-kernel run wastes tens of minutes before the mismatch surfaces
  // (or worse, reports answers from the wrong solver) — fail here.
  {
    std::vector<std::string> cliErrors;
    const bool flowsToActive = CFLFlowsTo && !CFLCompositional;
    if (CFLFlowsTo && CFLCompositional)
      cliErrors.push_back(
          "--cfl-flows-to requires --cfl-compositional=false: the flows-to "
          "solver is monolithic, and per-TU compositional mode (the "
          "default) silently ignores it");
    auto requireFlowsTo = [&](bool isSet, const char *flag) {
      if (isSet && !flowsToActive)
        cliErrors.push_back(std::string(flag) +
                            " only affects the flows-to solver and would be "
                            "silently ignored: add --cfl-flows-to "
                            "--cfl-compositional=false");
    };
    requireFlowsTo(CFLLazyMint, "--cfl-lazy-mint");
    requireFlowsTo(CFLFlowsToIncremental, "--cfl-flows-to-incremental");
    requireFlowsTo(CFLFlowsToSlice, "--cfl-flows-to-slice");
    requireFlowsTo(CFLResidueCopies, "--cfl-residue-copies");
    requireFlowsTo(CFLConflationReport, "--cfl-conflation-report");
    requireFlowsTo(CFLRootRelevance, "--cfl-root-relevance");
    requireFlowsTo(CFLProbeRodataJoins, "--cfl-probe-rodata-joins");
    requireFlowsTo(CFLProbeOriginSplit, "--cfl-probe-origin-split");
    requireFlowsTo(CFLProbeOpsMono, "--cfl-probe-ops-mono");
    requireFlowsTo(CFLProbeBlobFormation, "--cfl-probe-blob-formation");
    requireFlowsTo(CFLCensusStrata, "--cfl-census-strata");
    requireFlowsTo(CFLProbeUserCopyAblate, "--cfl-probe-usercopy-ablate");
    requireFlowsTo(CFLCertUserCopy, "--cfl-cert-usercopy");
    requireFlowsTo(CFLConfirmSinks, "--cfl-confirm-sinks");
    requireFlowsTo(CFLSinkInstr, "--cfl-sink-instr");
    requireFlowsTo(CFLCensusPtrToInt, "--cfl-census-ptrtoint");
    requireFlowsTo(CFLCensusTracepoint, "--cfl-census-tracepoint");
    requireFlowsTo(CFLCensusTypeRej, "--cfl-census-type-rej");
    requireFlowsTo(CFLCensusExternBound, "--cfl-census-extern-bound");
    // Adopted identity-channel models (tasks #35/#36, ADOPTED
    // 2026-08-03): default ON in the canonical flows-to mode, opt out
    // with --cfl-tracepoint-keys=false / --cfl-static-ops-tables=false.
    // Outside flows-to they AUTO-DISABLE unless explicitly requested —
    // their graph-build severs are only sound paired with the
    // answer-level resolution loop.
    if (!flowsToActive) {
      if (CFLTracepointKeys.getNumOccurrences() == 0)
        CFLTracepointKeys = false;
      if (CFLStaticOpsTables.getNumOccurrences() == 0)
        CFLStaticOpsTables = false;
      if (CFLPreSolveCone.getNumOccurrences() == 0)
        CFLPreSolveCone = false;
    }
    requireFlowsTo(CFLTracepointKeys, "--cfl-tracepoint-keys");
    requireFlowsTo(CFLStaticOpsTables, "--cfl-static-ops-tables");
    requireFlowsTo(CFLRodataCopy, "--cfl-rodata-copy");
    requireFlowsTo(CFLCensusIcallShape, "--cfl-census-icall-shape");
    requireFlowsTo(CFLProbeBornHub, "--cfl-probe-born-hub");
    requireFlowsTo(CFLPreSolveExact, "--cfl-presolve-exact");
    requireFlowsTo(CFLPreSolveCone, "--cfl-presolve-cone");
    requireFlowsTo(CFLJoinCone, "--cfl-join-cone");
    requireFlowsTo(CFLCensusCouplers, "--cfl-census-couplers");
    requireFlowsTo(CFLCensusNexus, "--cfl-census-nexus");
    requireFlowsTo(!CFLNexusFields.empty(), "--cfl-nexus-fields");
    requireFlowsTo(CFLBatchRoots > 0, "--cfl-batch-roots");
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
    // Incremental cross-iteration solving (task #43, km-validated
    // 2026-08-07): EXACT for FI configs (byte-identical, faster, bidi
    // cone re-admit fixed) but DIVERGENT under field sensitivity
    // (pool-smear, -504/+0 at km all+ids, bidi-independent). Enable by
    // default inside the validated envelope; refuse explicit requests
    // outside it.
    {
      const bool fsConfig =
          CFLFieldBuckets > 0 || !CFLNexusFields.empty();
      if (CFLFlowsToIncremental && fsConfig && !CFLPreSolveOnce) {
        errs() << "ERROR: --cfl-flows-to-incremental is not exact under "
                  "field sensitivity against the EAGER pre-solve pin: the "
                  "task-#43 divergence (-504 opt_pre_handler) is pool-smear "
                  "manufactured by the post-wiring pre-solve re-run, which "
                  "incremental never executes (attributed 2026-08-16). "
                  "Add --cfl-presolve-once to compare against the "
                  "smear-free pin, or drop the fs flags\n";
        exit(1);
      }
      if (CFLFlowsToIncremental && fsConfig && CFLPreSolveOnce)
        errs() << "FlowsTo: fs + incremental + presolve-once — validating "
                  "against the presolve-once scratch pin (A/B-gated "
                  "combo, 2026-08-16)\n";
      // Re-validated 2026-08-12 at HEAD (field filter retired,
      // percpu-gated identity rules): km incremental == from-scratch,
      // 160,945 pairs, zero diff both directions. A false divergence
      // alarm during the fs13 investigation came from comparing runs
      // of DIFFERENT binary vintages (filter-active incremental vs
      // filter-retired scratch) — vintage discipline matters: only
      // same-binary pins may be diffed.
      if (flowsToActive && !fsConfig &&
          CFLFlowsToIncremental.getNumOccurrences() == 0 &&
          CFLBatchRoots == 0 && !CFLLazyMint && !CFLOriginBundles) {
        CFLFlowsToIncremental = true;
        errs() << "FlowsTo: incremental cross-iteration solving "
                  "auto-enabled (FI config, #43-validated envelope; "
                  "re-validated at HEAD 2026-08-12); "
                  "--cfl-flows-to-incremental=false to opt out\n";
      }
    }
    if (CFLBatchRoots > 0 &&
        (CFLOpsPairs || CFLRodataCopy || CFLJoinCone)) {
      errs() << "ERROR: --cfl-batch-roots is untested with the "
                "protected-cell machinery (--cfl-ops-pairs/"
                "--cfl-rodata-copy/--cfl-join-cone) — prot state is not "
                "in the batch event protocol\n";
      exit(1);
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
    if (CFLJoinCone && !CFLPreSolveCone) {
      errs() << "ERROR: --cfl-join-cone needs the presolve cone "
                "(--cfl-presolve-cone)\n";
      exit(1);
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
    if (CFLCertUserCopy && CFLProbeUserCopyAblate) {
      errs() << "ERROR: --cfl-cert-usercopy tags the very edges "
                "--cfl-probe-usercopy-ablate severs; the flags are "
                "mutually exclusive\n";
      exit(1);
    }
    if (!CFLProbeStratumAblate.empty() && !CFLFlowsTo) {
      errs() << "ERROR: --cfl-probe-stratum-ablate requires --cfl-flows-to\n";
      exit(1);
    }
    if (!CFLProbeSinkAblate.empty() && !CFLFlowsTo) {
      errs() << "ERROR: --cfl-probe-sink-ablate requires --cfl-flows-to\n";
      exit(1);
    }
    if (CFLProposeOpsSt && !CFLOpsPairs) {
      errs() << "ERROR: --cfl-propose-ops-st requires --cfl-ops-pairs "
                "(proposals derive from the certification walk)\n";
      exit(1);
    }
    requireFlowsTo(!CFLAblateMints.empty(), "--cfl-ablate-mints");
    requireFlowsTo(CFLFlowsToMaxIters.getNumOccurrences() > 0,
                   "--cfl-flows-to-max-iters");
    requireFlowsTo(CFLSolverThreads.getNumOccurrences() > 0,
                   "--cfl-solver-threads");
    requireFlowsTo(CFLSolverBlock.getNumOccurrences() > 0,
                   "--cfl-solver-block");
    if (!cliErrors.empty()) {
      for (const auto &e : cliErrors)
        errs() << argv[0] << ": CLI sanity: " << e << "\n";
      return 1;
    }
  }

  if (MemLimitMode != "rss" && MemLimitMode != "as" && MemLimitMode != "off") {
    errs() << "ERROR: --mem-limit-mode must be rss, as, or off\n";
    return 1;
  }
  if (MemLimitPct > 0 && MemLimitMode != "off") {
    long pages = sysconf(_SC_PHYS_PAGES);
    long pageSize = sysconf(_SC_PAGE_SIZE);
    if (pages > 0 && pageSize > 0) {
      rlim_t totalBytes = (rlim_t)pages * pageSize;
      rlim_t limitBytes = totalBytes * std::min(MemLimitPct.getValue(), 100) / 100;
      if (MemLimitMode == "as") {
        struct rlimit rl;
        rl.rlim_cur = rl.rlim_max = limitBytes;
        if (setrlimit(RLIMIT_AS, &rl) == 0) {
          Diag << "Memory limit set to " << (limitBytes >> 30) << " GB ("
               << MemLimitPct << "% of " << (totalBytes >> 30)
               << " GB RAM, RLIMIT_AS)\n";
        } else {
          errs() << "Warning: failed to set memory limit\n";
        }
      } else {
        // RSS watchdog: poll resident size and fail LOUD before the
        // kernel OOM-killer picks a victim. Unlike RLIMIT_AS this
        // measures memory actually used — allocator arena
        // reservations, transient vector doublings, fragmentation and
        // mapped bitcode files do not count (the big-machine run died
        // at 289GB RSS under a 560GB AS cap on a 700GB box).
        Diag << "Memory limit set to " << (limitBytes >> 30) << " GB ("
             << MemLimitPct << "% of " << (totalBytes >> 30)
             << " GB RAM, RSS watchdog)\n";
        KAMemLimitRssBytes = (uint64_t)limitBytes;
        kaStartRssWatchdog();
      }
      // Disable core dumps — a core from a memory-exhausted process is huge
      struct rlimit rc;
      rc.rlim_cur = rc.rlim_max = 0;
      setrlimit(RLIMIT_CORE, &rc);
      // Handle allocation failure in any thread (including solver workers)
      std::set_new_handler([] {
        errs() << "ERROR: Out of memory. Increase --mem-limit or reduce input size.\n";
        _exit(1);
      });
    }
  }
  SMDiagnostic Err;

  // Loading modules
  Diag << "Total " << InputFilenames.size() << " file(s)\n";

  for (unsigned i = 0; i < InputFilenames.size(); ++i) {
    // use separate LLVMContext to avoid type renaming
    Diag << "Input Filename : "<< InputFilenames[i] << "\n";

    LLVMContext *LLVMCtx = new LLVMContext();
    std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

    if (M == NULL) {
      errs() << argv[0] << ": error loading file '"
        << InputFilenames[i] << "'\n";
      continue;
    }

    Module *Module = M.release();
    StringRef MName = StringRef(strdup(InputFilenames[i].data()));
    GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
    GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

    doBasicInitialization(Module);
  }

  // one more preprocessing to clear defined global variables and functions
  for (auto &[id, gv] : GlobalCtx.Gobjs) { GlobalCtx.ExtGobjs.erase(id); }
  for (auto &[id, f] : GlobalCtx.Funcs) { GlobalCtx.ExtFuncs.erase(id); }

  // Initialize node factory
  GlobalCtx.nodeFactory.setStructAnalyzer(&GlobalCtx.structAnalyzer);
  GlobalCtx.nodeFactory.setGobjMap(&GlobalCtx.Gobjs);
  GlobalCtx.nodeFactory.setExtGobjMap(&GlobalCtx.ExtGobjs);
  GlobalCtx.nodeFactory.setFuncMap(&GlobalCtx.Funcs);
  GlobalCtx.nodeFactory.setExtFuncMap(&GlobalCtx.ExtFuncs);

  // Main workflow

  // Data-driven Z_P selection (--cfl-field-buckets-auto): modules are
  // loaded, so census the fn-ptr slot offsets and pick the smallest
  // prime meeting the residual target. Explicit --cfl-field-buckets
  // takes precedence.
  if (CFLFieldBucketsAuto) {
    if (CFLFieldBuckets.getNumOccurrences() > 0) {
      errs() << "FieldBucketsAuto: explicit --cfl-field-buckets="
             << CFLFieldBuckets << " wins; auto selection skipped\n";
    } else {
      std::map<std::string, std::set<uint64_t>> slots;
      kaCollectFnPtrOffsets(
          GlobalCtx.Modules,
          [&](StringRef sName, uint64_t off, StringRef) {
            slots[sName.str()].insert(off);
          });
      uint64_t totalPairs = 0;
      for (auto &kv : slots) {
        uint64_t n = kv.second.size();
        totalPairs += n * (n - 1) / 2;
      }
      auto residualAt = [&](unsigned P) {
        uint64_t coll = 0;
        for (auto &kv : slots) {
          std::map<uint64_t, uint64_t> res;
          for (uint64_t o : kv.second)
            res[o % P]++;
          for (auto &rc : res)
            coll += rc.second * (rc.second - 1) / 2;
        }
        return coll;
      };
      auto isPrime = [](unsigned n) {
        if (n < 2) return false;
        for (unsigned d = 2; d * d <= n; d++)
          if (n % d == 0) return false;
        return true;
      };
      unsigned chosen = 0;
      uint64_t chosenColl = 0;
      const uint64_t budget =
          totalPairs * (uint64_t)CFLAutoBucketsResidualBP / 10000;
      for (unsigned P = 11; P <= CFLAutoBucketsMax; P++) {
        if (!isPrime(P)) continue;
        uint64_t c = residualAt(P);
        if (c <= budget) { chosen = P; chosenColl = c; break; }
      }
      if (chosen == 0) {
        // No prime within the cap meets the target: take the best
        // prime under the cap and say so loudly (no silent fallback).
        uint64_t bestC = UINT64_MAX;
        for (unsigned P = 11; P <= CFLAutoBucketsMax; P++) {
          if (!isPrime(P)) continue;
          uint64_t c = residualAt(P);
          if (c < bestC) { bestC = c; chosen = P; }
        }
        chosenColl = bestC;
        errs() << "WARNING: FieldBucketsAuto: residual target "
               << CFLAutoBucketsResidualBP << "bp needs P > cap "
               << CFLAutoBucketsMax << "; taking P=" << chosen
               << " with " << chosenColl << "/" << totalPairs
               << " colliding same-struct pairs\n";
      }
      CFLFieldBuckets = chosen;
      errs() << "FieldBucketsAuto: P=" << chosen << " ("
             << slots.size() << " structs, " << totalPairs
             << " same-struct offset pairs, " << chosenColl
             << " colliding at P = "
             << (totalPairs ? 10000.0 * chosenColl / totalPairs : 0.0)
             << "bp; cap " << CFLAutoBucketsMax << ")\n";
    }
  }

  // CFL-reachability edge construction
  if (GrammarFile.empty()) {
    if (!GlobalCtx.edgeBuilder.initializeGrammar(
            buildP2GrammarWithFields(CFLFieldBuckets))) {
      errs() << "Failed to initialize CFL edge builder with default grammar\n";
    }
  } else {
    if (!GlobalCtx.edgeBuilder.initializeGrammar(GrammarFile)) {
      errs() << "Failed to initialize CFL edge builder with grammar file: " << GrammarFile << "\n";
    }
  }

  std::unique_ptr<LLMClient> LLM;
  if (!LLMServerHost.empty()) {
    if (LLMServerPort == 0) {
      WARNING("Ignoring --llm-server-host because --llm-server-port is 0\n");
    } else {
      std::string Endpoint = "http://" + LLMServerHost + ":" +
                             std::to_string(LLMServerPort) +
                             "/v1/chat/completions";
      LLMClientConfig LLMConfig;
      LLMConfig.Enabled = true;
      LLMConfig.Endpoint = Endpoint;
      LLM = std::make_unique<LLMClient>(std::move(LLMConfig));
      Diag << "LLM server endpoint: " << Endpoint << "\n";
    }
  }

  if (IRCensusOpt || IRCensusStrict || !IRCensusOut.empty()) {
    IRCensusResult CR =
        runIRCensus(&GlobalCtx, IRCensusOut, /*printTables=*/IRCensusOpt);
    if (IRCensusStrict && CR.undispKinds > 0) {
      errs() << "IR-CENSUS STRICT: closed-world violated — "
             << CR.undispKinds << " undispositioned construct kind(s):\n";
      for (const std::string &N : CR.undispNames)
        errs() << "IR-CENSUS STRICT:   " << N << "\n";
      errs() << "IR-CENSUS STRICT: the edge builder's default visitor is a "
                "silent no-op; refusing to analyze a corpus it has no "
                "disposition for\n";
      abort();
    }
    if (IRCensusOpt)
      return CR.undispKinds > 0 ? 1 : 0;
    // strict/out without --ir-census: gate passed, continue to analysis
  }

  // Kerneldoc INVOKE mining: standalone proposer stage, exits after.
  if (!InvokeProposalsFile.empty()) {
    if (KernelSrcTree.empty()) {
      errs() << "Error: --invoke-proposals requires --kernel-src\n";
      return 1;
    }
    if (!InvokeMineDry && !LLM) {
      errs() << "Error: --invoke-proposals requires --llm-server-host and "
                "--llm-server-port (or --invoke-mine-dry)\n";
      return 1;
    }
    queryInvokeCandidates(&GlobalCtx, LLM.get(), KernelSrcTree,
                          InvokeProposalsFile, InvokeMineDry);
    return 0;
  }

  // LLM query / file loading for allocator candidates
  if (QueryLLM) {
    if (!LLM) {
      errs() << "Error: --query-llm requires --llm-server-host and --llm-server-port\n";
      return 1;
    }
    for (auto &[M, Name] : GlobalCtx.Modules) {
      queryAllocatorCandidates(&GlobalCtx, LLM.get(), M);
    }
    if (!AllocatorFile.empty())
      saveAllocatorResults(&GlobalCtx, AllocatorFile);
    return 0;
  } else {
    // If not querying LLM, load candidates from files if provided
    // loadAllocatorFile returns: 1 = loaded, 0 = file not available, -1 = parse error
    bool allocLoaded = !AllocatorFile.empty() && loadAllocatorFile(&GlobalCtx, AllocatorFile) > 0;
    if (!allocLoaded && LLM) {
      for (auto &[M, Name] : GlobalCtx.Modules) {
        queryAllocatorCandidates(&GlobalCtx, LLM.get(), M);
      }
    }
  }
  // load container candidates from file or query LLM
  if (!ContainerFile.empty()) {
    loadContainerFile(&GlobalCtx, ContainerFile);
  }

  if (CFLCompositional && !CFLGlobalDedup) {
    WARNING("--cfl-compositional requires --cfl-global-dedup; forcing it on\n");
    CFLGlobalDedup = true;
  }

  CallGraphPass CGPass(&GlobalCtx);
  auto tRun = std::chrono::steady_clock::now();
  CGPass.run(GlobalCtx.Modules);
  auto tRunEnd = std::chrono::steady_clock::now();
  Diag << "TIMER CGPass.run "
       << std::chrono::duration_cast<std::chrono::milliseconds>(tRunEnd - tRun).count()
       << " ms\n";

  // Run compositional CFL solve if requested
  if (CFLCompositional) {
    auto tComp = std::chrono::steady_clock::now();
    if (!CGPass.runCompositionalSolve()) {
      errs() << "Compositional solve failed\n";
      return 1;
    }
    Diag << "TIMER runCompositionalSolve "
         << std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - tComp).count()
         << " ms\n";
  }

  if (!CFLEdgeOutput.empty()) {
    GlobalCtx.edgeBuilder.outputEdgesToFile(CFLEdgeOutput);
  }

  if (!CallGraphJSON.empty()) {
    CGPass.dumpCallGraphJSON(CallGraphJSON);
  }
  if (!VSnapshotOutput.empty()) {
    CGPass.dumpVSnapshot(VSnapshotOutput);
  }
  if (!IRSidecarDir.empty()) {
    IRSidecarExporter Sidecar(&GlobalCtx);
    Sidecar.dump(IRSidecarDir);
  }

  if (!AllocatorFile.empty())
    saveAllocatorResults(&GlobalCtx, AllocatorFile);

  return 0;
}
