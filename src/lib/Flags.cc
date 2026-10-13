/*
 * Command-line options shared by KAMain and the CFL baseline (KABaseline).
 * Each binary's own options live next to its main(); Flags.h declares
 * these for the analysis code.
 *
 * Copyright (C) 2015 - 2026 Chengyu Song
 *
 * For licensing details see LICENSE
 */

#include <llvm/Support/CommandLine.h>

#include <string>

#include "Flags.h"

#ifndef KA_DEFAULT_SUMMARIES
#error "KA_DEFAULT_SUMMARIES (path of func_summaries.txt) is set by CMake"
#endif

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

cl::opt<bool> CFLTraceFirst(
  "cfl-trace-first",
  cl::desc("With --cfl-trace-func: log only the first arrival of each "
           "traced root at each class (bounded by the class count, no "
           "event cap), which is what a backward chain walk reads"),
  cl::init(false));

cl::opt<std::string> CFLTraceFptr(
  "cfl-trace-fptr",
  cl::desc("After the flows-to fixpoint, dump a backward slice from the "
           "fptr class of icalls in functions whose name contains this "
           "substring, annotated with traced-root presence, to localize "
           "where a flow is severed"),
  cl::init(""));

cl::opt<bool> CFLChannelCone(
  "cfl-channel-cone",
  cl::desc("With --cfl-channel-cells: wire channels only for cells that "
           "can influence some indirect call's callee expression "
           "(backward over a/f edges with Steensgaard may-alias jumps and "
           "owner-pointer hops). Answer-preserving by construction; "
           "=false wires every cell"),
  cl::init(true));

cl::opt<bool> CFLExtGlobalsOwnIdentity(
  "cfl-ext-globals-own-identity",
  cl::desc("Whole-program mode: every declared-but-undefined global gets "
           "its own node and cell (as PointTo does) instead of the "
           "universal pointer, so stores into one extern global are not "
           "read back from every other; the cell's content stays an "
           "unknown (identity) object. Linker-bounds symbols keep the "
           "--cfl-linker-arrays treatment. Ignored under "
           "--cfl-compositional, where an extern global may be defined by "
           "an unseen TU. =false restores the universal fallback "
           "(pre-2026-09-16 behaviour)"),
  cl::init(true));

cl::opt<bool> CFLReachable(
  "cfl-reachable",
  cl::desc("Reachability-driven body processing: a function's edges are "
           "emitted only once the function is reached from an entry "
           "(--cfl-entry-list; default: main and llvm.global_ctors) "
           "through a direct call, a resolved indirect call, or a summary "
           "callback binding. Closed-world premise: an unreached body "
           "never runs, so it neither emits flows nor holds external "
           "inputs. Unreached address-taken functions are ledgered"),
  cl::init(false));

cl::opt<std::string> CFLEntryList(
  "cfl-entry-list",
  cl::desc("--cfl-reachable: file with one entry function name per line "
           "(library exports, kernel asm-called functions)"),
  cl::init(""));

cl::opt<bool> CFLKeyIdentity(
  "cfl-key-identity",
  cl::desc("With --cfl-channel-cells: identity of never-written content "
           "per channel key instead of per read-access cell. No identity "
           "root is minted for any dereference cell; when a channel (o,s) "
           "is created for an EXTERNAL origin o (formal without callers, "
           "extern global, synthetic value, or another key identity) one "
           "identity origin is minted into it (a key identity's own "
           "channels get the identity itself back: depth-one self loop). "
           "Heap, stack and defined-global fields with no writer read as "
           "empty. Design: docs/channel-cells-design.md, Lean "
           "ChannelCells.handle_*"),
  cl::init(false));

cl::opt<std::string> CFLClonePerCaller(
  "cfl-clone-per-caller",
  cl::desc("Comma-separated function names to expand per call site at load "
           "time (each direct call site gets its own clone; names are "
           "processed in order, so a later name is cloned per the clones "
           "of an earlier one). The load-time equivalent of a per-call-site "
           "summary for a small generic helper such as linked_list_append: "
           "its allocation sites and formals become per site. Experiment "
           "instrument; the original is erased when no use remains"),
  cl::init(""));

cl::opt<std::string> CFLDumpClass(
  "cfl-dump-class",
  cl::desc("After the flows-to fixpoint, for every solver class whose name "
           "contains this substring: size, and its members grouped by "
           "function (count per function, a few member names), plus how "
           "many members are channel/read-half nodes. Answers 'why is X in "
           "one class with Y' when the union is an SCC merge, which the "
           "tracers do not record"),
  cl::init(""));

cl::opt<std::string> CFLDumpSCC(
  "cfl-dump-scc",
  cl::desc("At each a-SCC collapse, for the first SCCs (up to 4) that "
           "contain a node whose name contains this substring: size, "
           "channel share, and the SHORTEST CYCLE through that node over "
           "the a / residue-0 f edges the collapse followed, node by node. "
           "Shows how an unexplained merge was built"),
  cl::init(""));

cl::opt<bool> CFLHolderIdentity(
  "cfl-holder-identity",
  cl::desc("With --cfl-channel-cells: a fresh allocation stored through a "
           "pointer q (`*q = alloc`, traced through casts and O0 spill "
           "reloads) gets one clone origin per holder key of q, so lists "
           "and tables created lazily at one site are one object per "
           "holder (sym->caller, sym->callee, a global head). The fresh "
           "pointer itself keeps the base identity: its stores feed every "
           "clone, its loads see every clone. Bounds: no clone for X or "
           "constant-data holder keys, at most 32 holder keys per "
           "fresh-store cell, none for merged cells. Design: "
           "docs/channel-cells-design.md; Lean ChannelCells.holder_*"),
  cl::init(false));

cl::opt<std::string> CFLTraceMeet(
  "cfl-trace-meet",
  cl::desc("Two origin names (comma-separated substrings of a function, "
           "global, alloca or allocation-call name such as "
           "_bfd_new_bfd::call:bfd_zmalloc) that must never alias: report "
           "the first classes that come to hold both, with each origin's "
           "derivation chain (edge kind, source class, residue) walked "
           "back to its seed — the exact place the analysis unions them"),
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
           "material for the manual channel pipeline). Default on (the reported configuration); =false to opt out"),
  cl::init(true));

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

cl::opt<bool> CFLRegFieldObj(
  "cfl-regfield-obj",
  cl::desc("OBJECT-population channels (the regfield re-founding, "
           "docs/rendezvous-keying-design.md): certify which ops "
           "GLOBALS can occupy an ops-pointer field (witnessed &global "
           "stores + initializer slots + install hops + copy closure; "
           "any computed/heap pointer or writable member refuses) and "
           "clamp two-level dispatch sites with the objects' "
           "initializer-slot fns — INCLUDING GEP-less slot-0 "
           "dispatches, the class fn-slot keys cannot see (carried the "
           "post-regfield fat tail: one 4,648-fn pool per site at 5.18 "
           "fs). Slot-exact: no-GEP = offset 0 by construction. "
           "Soundness schema: proof/lean Channels.objclamp_sound. "
           "Requires --cfl-regfield-apply machinery (same walk). Default on (the reported configuration); =false to opt out"),
  cl::init(true));

cl::opt<bool> CFLNamedPlanes(
  "cfl-named-planes",
  cl::desc("Named cells (docs/named-cells-design.md): a store through a "
           "named struct field also files its value in a shadow cell for "
           "that field name, every other write into a cell also lands in "
           "the cell's unnamed shadow, and a load through a field name "
           "reads only those two shadows instead of the whole cell. "
           "Merged cells keep their content by name. Removal-only "
           "against the default (Lean NamedCells.named_sound_fderiv); "
           "soundness against the exact semantics assumes no type "
           "punning between named accesses (named_read_sound3)"),
  cl::init(false));

cl::opt<std::string> CFLNamedUntyped(
  "cfl-named-untyped",
  cl::desc("With --cfl-named-planes: what a write into a cell through an "
           "untyped pointer (no struct position: void *, char *, an "
           "unknown container) does to the field-name certificate. "
           "'count' (default): it opens no name; such writes are the "
           "counted blind spot, reported per run, the assumption the "
           "field tables make. 'open': it opens every name, so no load "
           "skips the unnamed plane (sound, plan decision 7)"),
  cl::init("count"));

cl::opt<bool> CFLAllocOrigins(
  "cfl-alloc-origins",
  cl::desc("Origins only from allocation (stack slots, globals, heap "
           "sites), functions and the environment (formals no call "
           "reaches, results of calls without a body or summary, extern "
           "globals): no identity root for the content of a cell nothing "
           "wrote, nor for a value with no incoming edge. An environment "
           "object's content is one content root per site, whose own "
           "content is itself. Sound under rule (a), no pointer made from "
           "external data (Lean Keys.keys_sound; plan 3.11)"),
  cl::init(false));

cl::opt<std::string> CFLRuleReport(
  "cfl-rule-report",
  cl::desc("Write the rule report to this file (plan 3.11 item 1): every "
           "place the program breaks the analysis's rules, (a) a pointer "
           "made from bytes that never were a pointer, (b) a named access "
           "reaching an object initialized as an incompatible struct, (c) "
           "an untyped write reaching a struct object, each with how the "
           "offending origin got there; and the unknowns, counted. "
           "Requires --cfl-alloc-origins with --cfl-named-planes (records "
           "every first arrival, single-threaded solve) or --cfl-cells (the "
           "cell solver's writer: also undefined behavior counted and the "
           "varargs keyed by format specifier)"),
  cl::init(""));

cl::opt<bool> CFLKeyCells(
  "cfl-key-cells",
  cl::desc("Memory as key cells (plan 3.13): one cell per key (origin, "
           "shift); a dereference writes into and reads from the key cells "
           "of its pointer's facts through directed edges (each cell split "
           "into a write half and a read half) and never merges with them; "
           "key cells never merge. Dereference nodes stay out of every "
           "merge (exact presolve, a-SCC collapse). Requires "
           "--cfl-alloc-origins. Checked per run: every dereference is "
           "wired to every key cell of its pointer's facts"),
  cl::init(false));

cl::opt<bool> CFLKeyHubs(
  "cfl-key-hubs",
  cl::desc("With --cfl-key-cells: wire through shared hubs. Memory nodes "
           "whose pointers have the same native fact set and the same name "
           "share one hub (a write half feeding the key cells of the set, "
           "a read half they feed), so the wiring costs the sum over "
           "distinct (set, name) of |set| instead of the sum over memory "
           "nodes. Exact: a node keeps its earlier hubs, whose sets are "
           "subsets of its current one"),
  cl::init(false));

cl::opt<bool> CFLWholeProgram(
  "cfl-whole-program",
  cl::desc("With --cfl-alloc-origins: the input is a whole program (an "
           "LTO link, the full kernel), so code outside it cannot write "
           "its globals or call its functions. Off (default): every "
           "externally visible global and every formal of an externally "
           "visible function is also an environment site, whose content "
           "is environment data (a partial corpus such as the km subset)"),
  cl::init(false));

cl::opt<unsigned> CFLEnvDepth(
  "cfl-env-depth",
  cl::desc("With --cfl-alloc-origins: how many levels of environment "
           "memory get their own content roots. The content at key (e, s) "
           "of an environment root e is a new root one level deeper; at "
           "this depth a root's content is itself. Any depth is sound; "
           "deeper keeps more environment objects apart (km: depth 1 "
           "welds +1,471 pairs, 2 and 3 agree)"),
  cl::init(2));

cl::opt<bool> CFLCensusTypeLabels(
  "cfl-census-type-labels",
  cl::desc("With --cfl-named-planes, after the fixpoint: label every "
           "object by the struct its initializing writes name (heap "
           "allocations through allocator and wrapper calls; globals and "
           "stack slots by declaration), then report how many untyped "
           "writes the labels type, and how many named accesses reach "
           "only objects consistent with their struct (where the type "
           "shortcut holds) versus objects labeled otherwise. "
           "Measurement only (docs/named-cells-design.md)"),
  cl::init(false));

cl::opt<std::string> CFLRegFieldWatch(
  "cfl-regfield-watch",
  cl::desc("With --cfl-regfield-apply: comma-separated fn names; log "
           "'RegFieldWatch: key K removes FN at caller' for every clamp "
           "that drops a watched fn — GT-loss attribution forensics"),
  cl::init(""));

cl::opt<bool> CFLChannelCells(
  "cfl-channel-cells",
  cl::desc("Pairwise-witnessed M (docs/channel-cells-design.md): route "
           "cell content through first-class (origin, shift) channel "
           "nodes instead of union-find cluster merges. Strictly tighter "
           "(removal-only vs clusters; Lean pair_le_cluster). v1: mono "
           "solve only — refuses batch mode, --cfl-verify-closure, and "
           "--cfl-solver-threads>1"),
  cl::init(false));

cl::opt<bool> CFLFilterLedger(
  "cfl-filter-ledger",
  cl::desc("Debug ledger: one 'FILTERED <mech> <key> <caller> "
           "@<file:line> -> <target>' line for EVERY pair a channel "
           "clamp removes (regfield fn-slot / rodata / obj). Join the "
           "lines against a ground truth (kernel GT pairs, fuzz-observed "
           "callsites) to certify no observed pair was filtered — a hit "
           "localizes the unsound removal to the responsible key. "
           "Answer-run instrument; output scales with removed pairs"),
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

cl::opt<bool> CFLDumpGTAux(
  "cfl-dump-gt-aux",
  cl::desc("MEASUREMENT-ONLY: dump DCALL (direct defined-callee call "
           "edges) and SCTCALL (direct __SCT__* trampoline calls) lines "
           "after module load, then exit. GT-matcher fidelity input "
           "(tools/gt-match.py --aux): devirtualized dispatches and "
           "static_call trampoline targets are otherwise creditable "
           "only via pool smear, which precision levers remove — "
           "surfacing phantom FN regressions. Config-independent"),
  cl::init(false));

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

cl::opt<bool> CFLCensusUnions(
  "cfl-census-unions",
  cl::desc("MEASUREMENT ONLY: for every union field of a struct (from "
           "debug info), its member accesses and whether a discriminator "
           "exists: a tag field (constant or flag bit) or a callback "
           "co-written with the union, one or two calls away; reads tested "
           "on the tag, and reads keyed by the facts their branches "
           "establish on stable fields. Adds no edges"),
  cl::init(false));

cl::opt<bool> CFLCensusNames(
  "cfl-census-names",
  cl::desc("MEASUREMENT ONLY (plan 3.23 item 6): with --cfl-named-planes, "
           "after the solve: (1) name-set width, the distinct labels of the "
           "objects each address pointer (and each void*/char* formal) "
           "reaches; (2) unnamed loads and stores by what their pointers "
           "reach (nothing / only labeled / mixed / only unlabeled objects); "
           "(3) container_of fan-out, the outer struct types per (embedded "
           "struct, offset) of the embedding table. Adds no edges"),
  cl::init(false));

cl::opt<std::string> CFLOutside(
  "cfl-outside",
  cl::desc("With --cfl-alloc-origins: what code the analysis has neither IR "
           "nor a summary for does. 'pure' (default, UNSOUND for such code): "
           "it writes nothing, calls nothing and keeps nothing it is given; a "
           "call to it returns no object, an uncalled function's formals "
           "take nothing from outside, extern globals hold only what the "
           "program writes. Whole programs only (--cfl-whole-program); a "
           "partial corpus refuses it. 'roots': each "
           "formal no call reaches, bodiless call result and vararg is an "
           "environment object with environment content (and, in a partial "
           "corpus, exported formals and visible globals)"),
  cl::init("pure"));

cl::opt<bool> CFLNameByTarget(
  "cfl-name-by-target",
  cl::desc("With --cfl-named-planes: an untyped write (no struct position "
           "on its address) is filed by what its pointer reaches, at solve "
           "time. While the pointer reaches only pointer variables (a stack "
           "or global object whose declared type is a pointer or an array of "
           "pointers), the write stays in the raw cell (unnamed reads see "
           "it) and out of the unnamed plane every named read also reads; "
           "it joins that plane as soon as the pointer reaches anything else"),
  cl::init(false));

cl::opt<bool> CFLKeyPartition(
  "cfl-key-partition",
  cl::desc("With --cfl-key-cells: key cells that one dereference reaches "
           "merge (as cluster mode merges cells) when their objects' labels "
           "are compatible, and stay apart when they are not; unlabeled "
           "objects form one group of their own. Labels as --cfl-weld-watch "
           "computes them. A coarsening of key cells, so sound; the cost "
           "should approach cluster mode"),
  cl::init(false));

cl::opt<unsigned> CFLWeldWatch(
  "cfl-weld-watch",
  cl::desc("Cluster mode: watch cell classes for welds of incompatible "
           "objects while solving. Objects are labeled before the solve (a "
           "global or stack slot by its declared struct, a heap allocation by "
           "the typed writes of the calls creating it); a class collects the "
           "labels of the keys it anchors. An event is a key anchored into, "
           "or a merge with, a class whose labels share no struct (offset-0 "
           "embedding counts as shared). Prints each event with its trigger "
           "and stops the run after N events (0 = off)"),
  cl::init(0));

cl::opt<bool> CFLUnionPathStable(
  "cfl-union-path-stable",
  cl::desc("With --cfl-union-keys=tag: a tag test keys a read when no path "
           "from the test to the read writes the tested tag bits or the "
           "union slot (plan 3.30 P2; else only program-wide stable tags), "
           "and a test on an earlier load of the same slot counts when the "
           "slot is not written in between (the reload clause)"),
  cl::init(true));

cl::opt<std::string> CFLUnionKeys(
  "cfl-union-keys",
  cl::desc("With --cfl-named-planes: give union accesses discriminator "
           "keys (plan 3.17): a union field gets one plane per key value, "
           "an access whose key is known reads/writes that plane, one whose "
           "key is unknown keeps today's wiring (every plane). 'off' (default), "
           "'callback' (keys inferred from co-written callbacks with "
           "correlated dispatch), 'single' (every union access the same key: "
           "a plumbing test), 'tag' (with --cfl-cells: a write keyed by "
           "the member it writes, a read by its member when its dominating "
           "tag tests rule out every other member's write)"),
  cl::init("off"));

cl::opt<std::string> CFLCensusUnionsDetail(
  "cfl-census-unions-detail",
  cl::desc("With --cfl-census-unions: for the union STRUCT.FIELD (or every "
           "union of STRUCT with STRUCT.), print each write's tag knowledge, "
           "each read's facts and verdict, uncovered writes and unkeyed reads"),
  cl::init(""));

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

cl::opt<bool> CFLProposeNoopSummaries(
  "cfl-propose-noop-summaries",
  cl::desc("Census: propose NOOP summaries by per-function proof of "
           "zero pointer-relevant transfer (conservative refusal: any "
           "icall/asm/non-noop callee/pointer or laundering store/"
           "pointer return refuses the candidate; fixpoint over "
           "callees). Prints NoopProp lines; adopt per-run via "
           "--cfl-adopt-proposed-summaries (pin/GT gated)"),
  cl::init(false));

cl::opt<bool> CFLWitnessAnswers(
  "cfl-witness-answers",
  cl::desc("Per-witness answer read (rung 1): recompute the final "
           "M-hop at load-shaped icall sites over the bipartite "
           "key-cell structure instead of the union-find cluster - "
           "content of exactly the cells sharing a key with the fptr "
           "cell (+ VX mirror). Sound: pooled planes upstream, pooled "
           "intersection downstream, pooled fallback anywhere "
           "unresolvable. Monolithic unbatched solves only"),
  cl::init(false));

cl::opt<bool> CFLProposeSolvedSummaries(
  "cfl-propose-solved-summaries",
  cl::desc("Stage A census: function-local abstract solve over the "
           "atom-grammar value vocabulary; extract interface atoms "
           "from the solved state (refuses only true interface "
           "escapes, in-body icalls, unsafe asm). Zero-atom successes "
           "become EMPTY-ATOM summaries (callsite wiring cut, body "
           "kept). Adopt per-run via --cfl-adopt-proposed-summaries. Default on (the reported configuration); =false to opt out"),
  cl::init(true));

cl::opt<bool> CFLProposeChainSummaries(
  "cfl-propose-chain-summaries",
  cl::desc("Census: derive driver-core CHAINREG/CHAINCALL channel "
           "summaries from IR evidence — a wrapper qualifies when it "
           "stores a bus_type global's address into a formal-rooted "
           "field AND passes that formal to driver_register/device_add "
           "(the key-constant frame); channel slot offsets come from "
           "the union of fn-bearing offsets in conforming callsites' "
           "static initializers (layout-correct per corpus). Prints "
           "ChainProp lines, reports MATCH/MISMATCH against existing "
           "file entries (never overrides them), refuses LOUDLY on "
           "fn-constant stores into the block (shim installers) or "
           "internal-linkage keys. Adopt per-run via "
           "--cfl-adopt-proposed-summaries; conservative bindings "
           "(REG f9 no-bind; CALL f0 additive). Default on (the reported configuration); =false to opt out"),
  cl::init(true));

cl::opt<bool> CFLAtomsGlobalStores(
  "cfl-atoms-global-stores",
  cl::desc("Allow generated atoms with GLOBAL deref targets "
           "(ST/MV*(*@g<-...)). QUARANTINED default-off: at 5.18 one "
           "such adoption welded the target global's cell cluster "
           "into the pool (+27k pairs); mechanism unpinned. Read-side "
           "@g atoms (ALIAS/LD) are unaffected"),
  cl::init(false));

cl::opt<std::string> CFLAdoptSkip(
  "cfl-adopt-skip",
  cl::desc("Comma-separated fn names excluded from per-run summary "
           "adoption (attribution bisection tool)"),
  cl::init(""));

cl::opt<bool> CFLAdoptProposedSummaries(
  "cfl-adopt-proposed-summaries",
  cl::desc("Adopt the provers' proposals as summaries FOR THIS RUN: "
           "NOOP + atom proofs are re-derived on the corpus being "
           "analyzed (atom byte offsets are layout-specific, so they "
           "never enter the shared func_summaries.txt). Runs the "
           "provers as a pre-pass before graph construction. Requires "
           "--func-summaries; monolithic mode only. Default on (the reported configuration); =false to opt out"),
  cl::init(true));

cl::opt<bool> CFLProposeAtomSummaries(
  "cfl-propose-atom-summaries",
  cl::desc("Census: propose transfer-atom summaries (ST/LD/MV/ALIAS "
           "with byte offsets) by per-function proof that ALL pointer "
           "effects are expressible over args/ret — conservative "
           "refusal (variable GEPs, two-level derefs, interior-pointer "
           "stores, unsafe callees, laundering). Runs atop the NOOP "
           "fixpoint for its safe-callee set. Prints AtomProp lines; "
           "adopt per-run via --cfl-adopt-proposed-summaries"),
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

cl::opt<bool> CFLProbeBlobFormation(
  "cfl-probe-blob-formation",
  cl::desc("MEASUREMENT-ONLY probe (task #31): log merge events while "
           "both classes are still small/nameable (min side >= 64 or "
           "size milestones), tagged by channel (join key origin, "
           "a-scc, protection paths). Report reconstructs the final "
           "giant class's growth history — causal channels instead of "
           "member names. Adds no edges"),
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

cl::opt<bool> CFLPoolCarves(
  "cfl-pool-carves",
  cl::desc("--cfl-cells: each carve of a certified pool (plan 3.53 rule 3: "
           "a bump, counter or header carve whose handle fields and chunk "
           "bases pass the checks) is its own allocation site; the "
           "confirmer takes carve results as fresh sources. Off: pools are "
           "recognized and reported only"),
  cl::init(true));

cl::opt<bool> CFLConfirmFresh(
  "cfl-confirm-fresh",
  cl::desc("Body-confirm PURE-FRESH allocation wrappers (returns trace "
           "only to fresh sources, no escapes, no pointer side effects) "
           "and promote them to allocator status, to fixpoint over "
           "wrapper chains — per-callsite object identities for their "
           "callers (task #17). Rejections tallied by reason"),
  cl::init(true));

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
           "summarized callsites. See func_summaries.txt. Default: the "
           "repository's func_summaries.txt (the reported configuration); "
           "--func-summaries= runs without a summary file"),
  cl::init(KA_DEFAULT_SUMMARIES));

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

cl::opt<std::string> CallGraphJSON(
  "callgraph-json", cl::desc("Export call graph to JSON file"), cl::init(""));

cl::opt<bool> CFLDumpCalleeMismatch(
  "cfl-dump-callee-mismatch",
  cl::desc("Per-callsite WARNING for callees found by type but not by CFL "
           "(can produce GBs of log on large inputs)"),
  cl::init(false));

cl::opt<std::string> CFLDumpAGraph(
  "cfl-dump-agraph",
  cl::desc("Write the flows-to solver's dense value-flow graph once per "
           "iteration to <prefix>.it<k>.{nodes,edges}, each edge "
           "classified by what it models (direct-call actual->formal, "
           "indirect-call actual->formal, return->callsite, store "
           "value->cell, cell->load, copy) for offline attribution of "
           "the value-flow components (which edge kind glues a giant "
           "component together). Diagnostic only"),
  cl::init(""));

cl::opt<bool> CFLDumpICalls(
  "cfl-dump-icalls",
  cl::desc("Dump one ICALL line per resolved (callsite, callee) pair; sort "
           "the lines to diff runs (5M+ lines on whole-kernel inputs)"),
  cl::init(false));

cl::opt<std::string> CFLDumpIcallsJson(
  "cfl-dump-icalls-json",
  cl::desc("Write per-callsite answers as JSON keyed by the callsite's "
           "debug location (\"file:line\": [target,...]) — the input "
           "format of the SoK-MLTA comparison harness. Includes "
           "EMPTY-answer icall sites (their AICT convention); sites "
           "without debug info are skipped with a counted warning. "
           "Dispatch (icall-classified) sites only; REGCALL "
           "re-attributions are not emitted"),
  cl::init(""));

cl::opt<std::string> CFLDumpTypeJson(
  "cfl-dump-type-json",
  cl::desc("MEASUREMENT-ONLY: write the TYPE-ONLY candidate set of every "
           "icall site (the filter's own isCompatible over address-taken "
           "functions) in the --cfl-dump-icalls-json format, so a site's "
           "flow answer can be compared with its type bound per site"),
  cl::init(""));

cl::opt<std::string> CFLDumpMerges(
  "cfl-dump-merges",
  cl::desc("MEASUREMENT-ONLY: write every solve-time class union of the "
           "final iteration with its cause (join key + the pointer class "
           "whose sweep issued it, or a-SCC collapse) plus a node-name "
           "table, so an offline replay can answer 'which union first put "
           "nodes X and Y in one class, and why' (scratch merges.py)"),
  cl::init(""));

cl::opt<bool> CFLLazyAddress(
  "cfl-lazy-address",
  cl::desc("Exact byte-offset addresses as facts, materialized on demand "
           "(docs/lazy-address-design.md): one fact plane, f-edges remap "
           "per bit, variable array indices are strided addresses, storage "
           "identity is the address. Implies --cfl-channel-cells; refuses "
           "batch, bidi-prune and the closure verifier"),
  cl::init(false));

cl::opt<bool> CFLCells(
  "cfl-cells",
  cl::desc("Cell solver (plan 3.26): facts are cells (origin, name), a "
           "name being the object's label and a byte offset folded by its "
           "layout (array elements onto element 0); loads and stores go "
           "through per-pointer hubs, never unify cells. Whole programs "
           "with --cfl-alloc-origins only"),
  cl::init(false));

cl::opt<bool> CFLCellUnify(
  "cfl-cell-unify",
  cl::desc("MEASUREMENT SWITCH, not a configuration of the reported analysis: --cfl-cells: unification by name. Two cells of one name that "
           "one node holds become one cell; different names never merge. "
           "false: every (object, offset) stays its own cell"),
  cl::init(false));

cl::opt<bool> CFLCellMergePtrs(
  "cfl-cell-merge-ptrs",
  cl::desc("MEASUREMENT SWITCH, not a configuration of the reported analysis: --cfl-cells: pointer nodes with equal sets (no function among "
           "them) become one node, at each periodic cycle collapse"),
  cl::init(false));

cl::opt<std::string> CFLCellStopAnswers(
  "cfl-cell-stop-answers",
  cl::desc("With --cfl-cell-census-at: write the partial state at the stop "
           "to this file (pops, cells, facts, and each indirect call's "
           "targets at that point), the cells gate's pin for a run stopped "
           "before its fixpoint (test/cells-gate.sh)"),
  cl::init(""));

cl::opt<unsigned> CFLCellCensusAt(
  "cfl-cell-census-at",
  cl::desc("MEASUREMENT ONLY: --cfl-cells stops propagating after this "
           "many pops over all iterations (0: never) and exits without "
           "answers; prints the confluence census (functions by "
           "formal/return width x direct call sites: clone candidates), or "
           "with --cfl-cell-why the why reports on the partial state"),
  cl::init(0));

cl::opt<std::string> CFLCellCensusFormal(
  "cfl-cell-census-formal",
  cl::desc("With --cfl-cell-census-at: FUNCTION:ARGNO whose held objects "
           "and names are listed"),
  cl::init(""));

cl::opt<std::string> CFLCellTraceObj(
  "cfl-cell-trace-obj",
  cl::desc("With --cfl-cell-census-formal: a backward path from the formal "
           "to the origin of an object whose description contains this"),
  cl::init(""));

cl::opt<bool> CFLCellReceivers(
  "cfl-cell-receivers",
  cl::desc("--cfl-cells: method calls as the program's own dispatch. A call "
           "whose callee is loaded through a path of field steps and loads "
           "from an argument p (p->f(p), p->ops->f(p), C++ p->vptr[k](p)) "
           "passes each object o at p only to the methods o's own path "
           "leads to; a method reached only through calls of one path "
           "shape reloads the holder from its receiver only as holders "
           "whose slot holds it (premise: the path is not rewritten in "
           "between). p is one value: one SSA value, or two loads of a "
           "non-escaping slot with no store between them"),
  cl::init(true));

cl::opt<bool> CFLConstructCensus(
  "cfl-construct-census",
  cl::desc("MEASUREMENT ONLY (plan 3.34 instrument 2): before the first "
           "solve, count the constructs that made soups so far, with "
           "examples and whether a summary covers them: allocator wrappers "
           "and pool allocators without a summary, generic containers "
           "(void* parameter stored into a field), method calls by path "
           "length, method-identity tests, unions with pointer members, "
           "varargs functions, struct copies through byte buffers"),
  cl::init(false));

cl::opt<bool> CFLCellSoupProfile(
  "cfl-cell-soup-profile",
  cl::desc("--cfl-cells instrument (plan 3.34): never stops; every fact "
           "landing on a node where its name is incompatible with the "
           "node's first name is foreign, and inherits the ENTRY of the "
           "fact it came from or, at the first such join, makes this node "
           "its entry. Reports entries and construct classes ranked by "
           "the foreign facts they explain, the hubs, and width per formal "
           "and per struct field"),
  cl::init(false));

cl::opt<bool> CFLCellWeldCensus(
  "cfl-cell-weld-census",
  cl::desc("--cfl-cell-soup-profile measurement (Part C input): a weld is the "
           "first fact of a second label arriving at a value node that held "
           "one label (byte storage, unlabeled or char, is a label of its own); welds are "
           "listed in arrival order (the first 20), each with its join, the "
           "mass of second-label facts descending from it at the profiler's "
           "stop, and, with --cfl-cell-why naming its object, its first-arrival "
           "chain"),
  cl::init(false));
cl::opt<bool> CFLCellLeakCensus(
  "cfl-cell-leak-census",
  cl::desc("--cfl-cell-soup-profile measurement: every non-char object's "
           "fact in a byte-named cell (i8[]) is walked back, along first "
           "arrivals, to the first edge where it entered a byte cell; the "
           "entries are classified (struct field, byte copy, buffer read as "
           "a struct, pointer stored into char storage, vararg or bodiless "
           "boundary, other) and ranked by the facts they explain at the "
           "profiler's stop point, with the inert check of byte cells"),
  cl::init(false));

cl::opt<unsigned> CFLCellSoupCap(
  "cfl-cell-soup-cap",
  cl::desc("--cfl-cell-soup-profile: stop (report, no answers) after this "
           "many foreign facts"),
  cl::init(20000000));

cl::opt<unsigned> CFLCellSoupTime(
  "cfl-cell-soup-time",
  cl::desc("--cfl-cell-soup-profile: stop (report, no answers) after this "
           "many seconds of propagation in one iteration (0: no limit); the "
           "report then includes the byte-copy cost table"),
  cl::init(0));

cl::opt<bool> CFLCellCollapse(
  "cfl-cell-collapse",
  cl::desc("--cfl-cells: collapse copy cycles during the solve (the static "
           "collapse before any fact moves always runs). Off is a measurement "
           "instrument: nodes keep their own facts, so --cfl-cell-why can "
           "follow a fact through what would be one merged class (slower)"),
  cl::init(true));

cl::opt<std::string> CFLCellWhy(
  "cfl-cell-why",
  cl::desc("--cfl-cells instrument: record the first cause of every fact "
           "arrival (edge, hub link, step, walk, any-offset, byte copy); at "
           "the heaviest byte copy, explain how its source pointer came to "
           "hold a cell of the object whose description contains this"),
  cl::init(""));
cl::opt<std::string> CFLCellWhyAt(
  "cfl-cell-why-at",
  cl::desc("--cfl-cell-why instrument: also explain why each node whose "
           "description contains this holds the --cfl-cell-why object"),
  cl::init(""));

cl::opt<bool> CFLCellOneLabel(
  "cfl-cell-one-label",
  cl::desc("MEASUREMENT ONLY: --cfl-cells with one cell per pointer: an "
           "arriving cell of the same name merges into the pointer's cell; "
           "the first cell of another name stops the solve and reports both "
           "cells and how each arrived"),
  cl::init(false));

cl::opt<unsigned> CFLCellOneLabelMax(
  "cfl-cell-one-label-max",
  cl::desc("--cfl-cell-one-label: collect this many name conflicts (each "
           "with the point where the two labels' paths meet) before "
           "stopping, keeping both labels at a conflict; prints the clone "
           "candidates (functions whose formal is a meet point)"),
  cl::init(1));

cl::opt<unsigned> CFLCellCap(
  "cfl-cell-cap",
  cl::desc("--cfl-cells: offset cells of an UNLABELED object before its "
           "further offsets become its any-offset cell (counted); a labeled "
           "object's cells are bounded by its layout"),
  cl::init(32));

cl::opt<unsigned> CFLLazyCap(
  "cfl-lazy-cap",
  cl::desc("--cfl-lazy-address: exact addresses minted per writable object "
           "of UNKNOWN size before further offsets become its range root "
           "(objects of known size up to 4096 bytes are uncapped: their "
           "in-bounds offsets are finite; identity roots: four times this; "
           "constant globals: at least 128)"),
  cl::init(32));

cl::opt<std::string> CFLLazyTraceObject(
  "cfl-lazy-trace-object",
  cl::desc("--cfl-lazy-address: log every address minted on objects whose "
           "name contains this substring (source address, label, edge)"),
  cl::init(""));

cl::opt<bool> CFLLazyTypedAccess(
  "cfl-lazy-typed-access",
  cl::desc("--cfl-lazy-address: a member step of struct S applied to an "
           "address whose object has an incompatible type yields no address "
           "(the union-member typed read, applied at the first typed use). "
           "Sound iff the program has no type confusion; every drop is a "
           "census conflict and is counted"),
  cl::init(false));

cl::opt<bool> CFLLazyTypeIdentity(
  "cfl-lazy-type-identity",
  cl::desc("--cfl-lazy-typed-access: identity roots (the unknown pointee of "
           "an unwritten cell) take the type of their first typed access, "
           "like heap objects; sound iff the underlying field is not a void* "
           "or union slot (census conflicts show where it is)"),
  cl::init(false));

cl::opt<bool> CFLChannelDemand(
  "cfl-channel-demand",
  cl::desc("With --cfl-channel-cells: demand-driven wiring. A read cell is "
           "wired to its keys' channels only once its value can reach an "
           "indirect call (static reverse closure from the callee operands, "
           "extended through every wired store); a store is wired to a key "
           "only once some relevant read demands that key. Deferred pends "
           "replay when demand or relevance arrives. Answer-preserving"),
  cl::init(false));

cl::opt<std::string> CFLDemandSite(
  "cfl-demand-site",
  cl::desc("Single-site query: only indirect-call sites whose file:line "
           "contains this string (or whose function has this name) seed "
           "demand relevance (--cfl-channel-demand) and lazy-mint "
           "relevance; at the end, a widening report walks the fact flow "
           "backward from the site's callee operand and names the classes "
           "where the fact set widens (>= 2x every in-neighbour). Answers "
           "for other sites are NOT valid in this mode"),
  cl::init(""));

cl::opt<bool> CFLVarargsStrict(
  "cfl-varargs-strict",
  cl::desc("Type filter: a NON-variadic callee behind a variadic-typed "
           "call (\"T (A, ...)\") must have exactly the call type's fixed "
           "parameter count. clang types an unprototyped (K&R) call as "
           "variadic with every actual as a fixed parameter, so K&R "
           "dispatch keeps its callees; only genuine \"(fmt, ...)\" "
           "prototypes lose fixed-arity candidates (nm-new: 66 sites, "
           "4,798 pairs). Default off: pins are measured without it"),
  cl::init(false));

cl::opt<std::string> IRSidecarDir(
  "ir-sidecar-dir",
  cl::desc("Directory to write per-bc IR fact sidecar JSON files (<bc>.facts.json)"),
  cl::init(""));

cl::opt<int> MemLimitPct(
  "mem-limit", cl::desc("Memory limit as a PERCENTAGE of physical RAM, not GB (0 = unlimited, "
                        "default 80): on a 1.5 TB machine 40 is about 594 GB, 2 about 30 GB; the "
                        "process exits when its resident size passes it (--mem-limit-mode)"),
  cl::init(80));

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
