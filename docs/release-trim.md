# Release trim: fix-or-remove ledger (started 2026-09-04)

Policy (user): no tombstones, no parked code — fix it or remove it.
History lives in git; the tree ships what works. Every removal is a
pure deletion of default-off paths, gated by cfl-smoke + the
canonical pin.

REMOVED:
- witness-taint (2026-09-04): retired experiment, falsified by
  design review + GT. Files deleted; flag deleted.
- incremental cross-iteration solving (2026-09-04): divergent at
  kernel corpora (docs/incremental-518-divergence.md); the fix is
  a perpetual seed-enumeration tax on every future edge kind for a
  ~20% wall win that the PROVEN-EXACT lazymint+bidi pair largely
  recovers. wireIncremental + flag + envelope guards deleted.
  incr_exact (Staging.lean) retained as the specification for any
  future reimplementation.
- origin-bundles (2026-09-04): parked feature (Gate 2 wall fail),
  default-off. Removed: epoch machinery + remapBits/expandBits +
  mintRoot/blame bridging + 3 flags (--cfl-origin-bundles,
  --cfl-bundle-epoch-facts, --cfl-bundle-probe), plus leftover
  incremental-wiring debris found by the warning sweep (growTo,
  parkedRoots, newAllocNodes, edgesConsumed, protBlameName2,
  solverCapN headroom). Bundles.lean + design doc stay as the
  record/spec. Gates: cfl-smoke 4/4; libpng old-vs-new
  byte-identical; km all+ids mono + batched old-vs-new
  byte-identical (same-day binaries, same corpus).
- superseded mechanisms (2026-09-04, trim pass 2): --cfl-ops-pairs
  (+ its step-2 receiver tightening, certifyOpsPairs walk, and
  --cfl-propose-ops-st proposer — existing func_summaries.txt
  entries it produced stay; generator lives in git),
  --cfl-rodata-copy, --cfl-join-cone, --cfl-probe-rodata-joins, and
  the ENTIRE protected-cell (prot) machinery they exclusively
  enabled (writer/reader/demote/collapse, protRid/protCls/coneIn,
  rootRodata/classIsRodata, blame censuses). Verified first:
  nothing canonical consumes prot (all three enablers default-off;
  protOn unreachable in every pinned config). --cfl-presolve-cone
  KEPT (its own mechanism; only its join-cone export removed).
  Latent placement bug fixed on the way: the StrataAblate ledger
  print lived inside the protOn block and only printed under prot
  configs. Gates: same battery as pass 1, all byte-identical.

QUEUED (each = its own gated pass):
1. Flag census for the wider trim — candidates by class:
   - one-off measurement probes that produced their numbers and
     are recorded in docs: ablate-mints/ablate-funcs, probe-*,
     census-* (KEEP the ones the paper's instruments still use:
     probe-blob-formation/ClassHist, census-couplers, gt dumps)
   - legacy/task-specific listed in cli-reference "Other" section
2. cli-reference.md regeneration after each pass (remove dead
   entries).
3. The trimmed tree then IS the FSE artifact base (anonymized).

## 2026-10-02: KAMain is the flows-to solver; the CFL baseline is its own binary

Plan: `docs/plan-named-cells.md` Part A (A.1, A.2). User decisions:
compositional and every saturation mode move to a CFL-reachability
baseline pass (`CFLCGPass`) built as a separate binary; GraCFL stays
vendored for it; the LLM code stays in the tree but KAMain no longer
uses it; KAMain's default is the reported ("full") configuration.

MOVED to `src/baseline/` (binary `release/baseline/KABaseline`):
monolithic saturation (old `doModulePass` tail), compositional mode
(`solveAndCompressPerTU`, `runCompositionalSolve`,
`compressConstraintGraph`, `computeVSCC`, compressed-graph cache and
its metadata), allocator discovery and icall resolution over the
saturated graph, V snapshots, fptr slicing, the grammar
(`Grammar.h`, was `Global.h`), `CFLEdgeBuilder` (now GraCFL's
labelled view of the constraint graph), `CompressedGraph`,
`VSnapshot`. Options that moved with them: `--cfl-compositional`,
`--cfl-compressed-output`, `--cfl-compressed-input`,
`--cfl-presolve-merge`, `--cfl-fptr-slice`, `--grammar-file`,
`--cfl-edge-output`, `--v-snapshot`, `--cfl-cache-strict`,
`--cfl-cache-repair`, `--cfl-cache-allow-duplicate-coverage`.
KABaseline refuses the options only the flows-to solver honors.

REPLACED: the presolve's GraCFL sub-closure (V-components of the
memory-free sublanguage) by `ka::valleyComponents` (`src/lib/SCC.h`;
statement and proof sketch in `proof/lean/GAPS.md`). Cross-checked
partition-identical against GraCFL on every configuration tried; 10-
50x faster on first passes. The five iterative Tarjans now share
`ka::tarjanSCC`. `CFLEdgeBuilder` in the shared code is replaced by
`ConstraintGraph` (`src/lib/ConstraintGraph.h`): typed forward edges
(copy, deref, field residue, field-any), inverses implied.

REMOVED from KAMain (passing one is an error naming the replacement):
`--cfl-flows-to` (the only mode), the eleven moved options above,
the LLM paths `--llm-server-host`, `--llm-server-port`,
`--query-llm`, `--invoke-proposals`, `--invoke-mine-dry`,
`--kernel-src`, and the LLM-result loaders `--allocator-file`,
`--container-file` (allocators and containers come from
`--func-summaries`). Dead code deleted: `dumpFuncPtrs`, `dumpGlobals`
(no callers), the edge builder's cycle breaking / edge reduction /
edge printing (no callers).

DEFAULTS CHANGED (KAMain only; KABaseline keeps the old ones):
`--cfl-propose-chain-summaries`, `--cfl-regfield-apply`,
`--cfl-regfield-obj`, `--cfl-propose-solved-summaries`,
`--cfl-adopt-proposed-summaries` default on; `--func-summaries`
defaults to the repository's `func_summaries.txt`
(`--func-summaries=` runs without one). Scripts state other
configurations with `ka_config` (`eval/env.sh`).

OUTPUT FIXES: `--callgraph-json` is deterministic (functions, callers
and callees were emitted in pointer order; an ID with several bodies,
a header's static inline function, now lists the callees of every
body instead of whichever pointer came first). `--ir-sidecar-dir` no
longer renumbers the module per printed operand (hours on single-
module programs; output unchanged). KAMain links jemalloc directly
(it was its allocator through GraCFL's link line) and no longer links
TBB or OpenMP.

