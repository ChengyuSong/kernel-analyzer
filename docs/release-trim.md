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

### Flag census (plan A.4, 2026-10-02)

Every option of both binaries after the split, by class. "Part B"
marks the raw material plan section 2.4 says to decide during Part B;
those are untouched here.

KEEP — inputs, outputs, driver: `<inputs>`, `--bc-list`, `--verbose`,
`--log-timestamps`, `--mem-limit`, `--mem-limit-mode`,
`--callgraph-json`, `--cfl-dump-icalls`, `--cfl-dump-icalls-json`,
`--ir-sidecar-dir`, `--ir-census`, `--ir-census-strict`,
`--ir-census-out`, `--cfl-clone-per-caller` (Part C).

KEEP — shipped solver and graph build: `--cfl-global-dedup`,
`--cfl-local-alloca-summary`, `--cfl-ext-globals-own-identity`,
`--cfl-linker-arrays`, `--cfl-static-call`, `--cfl-printf-vararg-sink`,
`--cfl-tracepoint-keys`, `--cfl-static-ops-tables`,
`--cfl-presolve-cone`, `--cfl-presolve-exact`, `--cfl-presolve-once`,
`--cfl-flows-to-max-iters`, `--cfl-iter-cap-ok`,
`--cfl-verify-closure`, `--cfl-varargs-strict`, `--cfl-reachable`,
`--cfl-entry-list`, `--cfl-bidi-prune`, `--cfl-lazy-mint`,
`--cfl-intern-planes`, `--cfl-intern-sweep`, `--cfl-join-fastpath`
(the last four are the exact-family ablations of eval/35 and eval/60),
`--cfl-witness-answers`, `--cfl-flows-to-slice`,
`--cfl-residue-copies`.

KEEP — threading, batching: `--cfl-solver-threads`,
`--cfl-solver-block`, `--cfl-batch-roots`, `--cfl-batch-workers`,
`--cfl-batch-spill`.

KEEP — summaries and their provers/confirmers: `--func-summaries`, the
five default-on mechanisms (`--cfl-propose-chain-summaries`,
`--cfl-propose-solved-summaries`, `--cfl-adopt-proposed-summaries`,
`--cfl-regfield-apply`, `--cfl-regfield-obj`),
`--cfl-propose-noop-summaries`, `--cfl-propose-atom-summaries`,
`--cfl-atoms-global-stores`, `--cfl-adopt-skip`, `--cfl-confirm-fresh`,
`--cfl-confirm-invoke`, `--cfl-census-invoke` (emits INVOKE proposal
lines for the confirmer: a summary-authoring tool),
`--cfl-census-extern-bound` (ranks unsummarized external callees: the
summary worklist for a new corpus).

KEEP — names (Part B grows these): `--cfl-regfield-report` (the
detector, plan 3.4), `--cfl-regfield-audit`, `--cfl-regfield-watch`,
`--cfl-filter-ledger`.

KEEP — certificates and contract gates: `--cfl-cert-usercopy`,
`--cfl-confirm-sinks`, `--cfl-sink-instr`.

KEEP — instruments the paper or Parts B/C use:
`--cfl-probe-blob-formation` (the RQ1 estimator, ClassHist),
`--cfl-census-couplers` (Part C), `--cfl-census-nexus` (Part B),
`--cfl-census-type-rej` and `--cfl-gt-type-census` (RQ2 type-rejection
evidence), `--cfl-dump-gt-aux` (eval/60), `--cfl-ablate-mints`,
`--cfl-ablate-funcs` (tools/dd-funcs.py), `--cfl-conflation-report`,
`--cfl-root-relevance`, `--cfl-cotravel-stats`, `--cfl-solver-profile`.

KEEP — trace and dump instruments: `--cfl-trace-func`,
`--cfl-trace-first`, `--cfl-trace-fptr`, `--cfl-trace-meet`,
`--cfl-trace-value`, `--cfl-dump-class`, `--cfl-dump-scc`,
`--cfl-dump-merges`, `--cfl-dump-agraph`, `--cfl-dump-type-json`,
`--cfl-dump-callee-mismatch`, `--cfl-dump-fnptr-offsets`.

PART B (decide there): `--cfl-field-buckets`,
`--cfl-field-buckets-auto`, `--cfl-auto-buckets-residual-bp`,
`--cfl-auto-buckets-max`, `--cfl-nexus-fields`, `--cfl-channel-cells`,
`--cfl-channel-cone`, `--cfl-channel-demand`, `--cfl-demand-site`,
`--cfl-key-identity`, `--cfl-holder-identity`, `--cfl-lazy-address`,
`--cfl-lazy-cap`, `--cfl-lazy-trace-object`, `--cfl-lazy-typed-access`,
`--cfl-lazy-type-identity`.

REMOVED — dead options (user decision 2026-10-02): `--dump-bid-mapping`,
`--dump-func-info`, `--dump-annotated-ir` were accepted but did nothing
since 3d84c19 (2026-02-12), when `--callgraph-json` replaced their
code. Older revisions keep them.

KABASELINE ONLY: `--cfl-compositional`, `--cfl-compressed-output`,
`--cfl-compressed-input`, `--cfl-presolve-merge`, `--cfl-fptr-slice`,
`--grammar-file`, `--cfl-edge-output`, `--v-snapshot`,
`--cfl-cache-strict`, `--cfl-cache-repair`,
`--cfl-cache-allow-duplicate-coverage`.

REMOVED — measurement probes (all MEASUREMENT-ONLY/UNSOUND, default
off; one commit each; the question and the recorded answer):
- `--cfl-probe-no-cell-identity`: size of the per-access identity-root
  web under pairwise cells; superseded by `--cfl-key-identity`
  (docs/channel-cells-design.md).
- `--cfl-probe-no-x-bridges`: do unknown-offset bridges decide nm-new?
  No: byte-identical to P=13, 63,202 pairs.
- `--cfl-probe-identity-join-ablate`: are identity-keyed joins the
  nm-new weld? They shatter the cluster (max keys 10,782 to 1,164) and
  tighten 305/1,453 sites, but the info site moves 51 to 50; width is
  field- and context-insensitivity (channel-cells campaign).
- `--cfl-probe-wildcard-ablate`: do unknown-offset wildcards weld?
  Ablating all 6,338 mints leaves the site at 74; inert on the AICT gap.
- `--cfl-probe-stratum-ablate`: does the phys/page stratum feed the
  kernel blob? Barely (-3% pre-solve); removals -216/+0 at movable_ops
  (docs/cfl-graph-explosion-and-scaling.md, task #32).
- `--cfl-probe-usercopy-ablate`: is user data a control channel? No:
  the user-boundary separation holds on the kernel (2026-08-01).
- `--cfl-probe-no-icall-wiring`: is resolution feedback the pooling
  engine? No: over still-resolved sites the mean moves 44.6 to 44.5.
- `--cfl-probe-no-int-stores`: integer-laundered stores? No change.
- `--cfl-probe-noformal-presolve`: formal confluence glues the born
  component (kernel 49,515 to 381); nm-new inert
  (docs/kernel-precision-killers.md).
- `--cfl-probe-born-hub`: is the born giant a few hubs? km V'
  component 41,350 members has a 41-node mutual-flow core; led to
  `--cfl-presolve-exact` and the cone hybrid.
- `--cfl-probe-witness-sep`: per-witness separation inside the giant
  (km fs13 W/cluster p50 = 0.0001); led to `--cfl-witness-answers`.
- `--cfl-probe-blob-grep`: name-filtered lineage events for the
  blob-formation probe; the attribution it served is done.
- `--cfl-probe-sink-ablate`: trace-payload sinks as fusion channels
  (kernel: one pre-fused hub; nm-new: 4 sites tighter); led to the
  reviewed sink model `--cfl-sink-instr`.
- `--cfl-probe-no-trans-join`: refusing transitive key joins zeroes
  1,218 nm-new sites; too destructive to be a design.
- `--cfl-probe-ops-mono`: ops-table monomorphism of two-level dispatch
  (task #30); led to the object tables (`--cfl-regfield-obj`).
- `--cfl-probe-origin-split`: same-origin binding is vacuous on the
  final quotient (km 1,047 icalls, D==1 everywhere; task #29).
- `--cfl-probe-block-hub-formals`: KallGraph's static hub block is not
  its precision source on nm-new (N=250 byte-identical, N=50 -23
  pairs, -2 GT).

REMOVED — measured dead ends: `--cfl-key-channels` and
`--cfl-identity-channels` (one mechanism; identity channels required
key channels). Constant-global channels are sound but answer-neutral
at the nm-new fixpoint (63,200 pairs, 2.2x slower); identity channels
reached 16.8 G facts before the first flush
(docs/channel-cells-design.md, "The BFD_SEND dispatch").

REMOVED — one-off censuses whose results are recorded:
`--cfl-census-carve` (docs/channel-cells-design.md),
`--cfl-census-fields` (task #29; superseded by the regfield detector),
`--cfl-census-strata` (task #32, with its stratum classifier),
`--cfl-census-ptrtoint` (task #33), `--cfl-census-tracepoint` (task
#35; sized the adopted tracepoint keys), `--cfl-census-icall-shape`
(task #37); all in docs/cfl-graph-explosion-and-scaling.md unless
noted.

Every removed option is an error in KAMain naming this ledger.
