# Implementation: Soundness Mechanisms and Performance Engineering

Paper-facing record of the implementation-level contributions (updated
2026-08-16). Two organizing principles ran through all of it:

1. **Soundness is never traded.** Anything we cannot prove is fixed or
   abandoned; syntactic masks over graph-derived answers are retired,
   not tuned. Unexpected states are assertions, not fallbacks.
2. **Optimizations must be exact, and exactness is checked, not
   assumed.** Every performance change ships with a byte-identical A/B
   against a pinned answer set (ICALL ∪ REGCALL pairs, same binary
   vintage, flag-matched), plus machine-checked theorems where the
   argument is structural. Changes that fail the gate are reverted
   with an in-code tombstone recording the measurement.

## 1. Exactness discipline

- **Pins.** Canonical answer sets per configuration (km FI 161,689;
  km fs13 150,742; km fs41 149,791 at current HEAD). Only same-binary,
  flag-matched pins are diffable; two historical false alarms came
  from vintage or flag mismatches (the fs13 150,120 pin is
  bidi-prune-conditioned; bidi is strictly tighter under fs, not
  answer-invariant).
- **Per-run certificates.** `--cfl-verify-closure` re-checks every
  solver rule non-incrementally at the fixpoint (C0–C5), seed presence
  under the mint policy (C6), and mint coverage at the final quotient
  (C7). Iteration caps that would truncate the fixpoint refuse to
  produce output unless the user explicitly accepts an UNSOUND-marked
  result.
- **Machine-checked core (proof/lean, no sorry/axioms).** Solver
  completeness against the grammar (`answers_complete`); lazy-mint
  staging confluence and the necessity of the catch-up round
  (`sderiv_catchup` + a seven-node counterexample showing restricted
  minting loses answers); batched-solving exactness via witness tables
  (`batched_exact`, `wderiv_sound`, `wderiv_restore` for spill
  restore); origin-bundle exactness (`bundle_exact` — a quotient of
  closure-row-equal origins preserves the closure member-by-member;
  `row_determined` — equal carried-base rows imply equal closure
  rows, licensing runtime full-state-hash tests). GAPS.md records the
  engineering layer each theorem sits on.
- **Assertions over fallbacks.** The bundle work demonstrated the
  policy's value twice in one day: an L1 cluster-equality assertion
  caught (a) a classic partition-refinement bug (group sizes must be
  snapshotted pre-split), and (b) a genuine theory gap — row equality
  does not imply cluster equality at a checkpoint, because the cluster
  registry is memoized join history whose row evidence a merge's
  joined-intersection erases. Both became part of the epoch test.

## 2. Soundness mechanisms

- **Field-filter retirement.** The historical field filter compared
  load keys against an under-approximated store-key inventory and
  deleted pairs on missing evidence — unsound (ground-truth
  process_one_work-family pairs were dynamically true). It was
  retired from the answer path; field discrimination now lives in the
  graph itself (shift-indexed residue planes, mod-P with prime P
  chosen by collision census). A census showed 96.7% of the filter's
  trim was cross-struct hub leakage — territory for sound channel
  mechanisms, not field sensitivity.
- **Field sensitivity as grammar, not filter.** Shift-composable
  labels (`f_r`, X wildcard) with container_of handled by residue
  arithmetic; fs answers are provably a refinement of FI (quotient
  homomorphism; fs ⊆ FI holds at every pin).
- **Integer-provenance completion.** ptrtoint/inttoptr flows are
  modeled to a closed ledger (0 unmodeled at km): int loads/stores,
  call results, cross-TU argument wiring (witness-gated), with
  retraction mirrors in call-edge removal. Field claims survive
  integer segments via segment-local tag-round-trip proving (memory
  and calls cannot compute, so offset arithmetic lives in register
  segments between provenance boundaries); consumers whose cones
  reach inttoptr are wildcarded when a segment is dirty. The percpu
  base-relocation invariant (declared, shared with the identity gate)
  keeps per-cpu rebasing shift-exact; genuinely unprovable cases
  (page-mask laundering, dynamic arithmetic) stay wildcards.
- **Transfer summaries with a dispatch-audit rule.** Allocator/copy
  summaries replace hardcoded lists; a summary is refused for any
  function whose body contains an indirect call (summarizing would
  starve the dispatch — measured: a pool-allocator summary silently
  removed all six real targets of a callback site). The v1 userspace
  pool-allocator block was withdrawn on exactly this evidence.
- **Sound instrumentation only.** Measurement modes that reroute
  joins (rodata probe, sink ablation) are flagged as unsound
  measurements and refused in combination with exactness-sensitive
  features.

## 3. Performance engineering (all byte-identical at the pins)

Three distinct layers, each with its own methods. The 2026-08
sequence took km fs41 from 4h13m to 1h32m (2.76x) and km fs13 to
23m; commit hashes anchor each mechanism.

### 3.1 Algorithm/scheduling level

- **Wave scheduling.** The drain processes worklist snapshots as
  topologically-ranked waves so each hot plane is streamed once per
  wave, with periodic in-drain a-SCC collapse and intern sweeps
  hooked at the sequential block boundaries.
- **Lazy minting + catch-up** (task #21): restricted-root drains with
  a convergence-time catch-up round; exactness machine-checked
  (`sderiv_catchup`), fact mass 48% of eager.
- **Origin-batched solving** (#40, f2a9b16): fact planes are pure
  derived state; only the union-find quotient, cluster keys and
  bridges couple batches. Drain K roots at a time, repeat rounds to
  merge-stability — memory becomes graph + one batch's planes, and
  the stop condition (stable merges, mints AND cluster keys) matches
  `batched_exact`'s closedness hypothesis.
- **Incremental cross-iteration solving** (#43, b82985d/cb2cfb5):
  from-scratch wiring iterations re-derive everything; incremental
  continues the fixpoint. Root-caused the stale-bidi-cone bug (cone
  oracle re-admission at wiring), validated exact for FI and
  auto-enabled there.
- **Cell-major join sweep** (f13f8d6). The join backlog filter did a
  ~350-cycle probe per (fact, cell) visit with 99.98% proven no-ops
  (9.0B skips vs 1.8M real joins). Inverting fact-major to cell-major
  answers the whole backlog per cell at word level: a read-only
  subset scan certifies "cluster already absorbed all of this", a
  word-ANDN materializes the residual. Join 69.5% → 33.1% of pop
  cycles; fs41 1.63x.
- **Wall decomposition over micro-optimization.** After the kernel
  fusion work, hardware counters (IPC 2.76, LLC misses ~1.4% of
  cycles) showed the solver at its compute floor — and timestamp
  decomposition exposed that 56% of the remaining fs41 wall was one
  hidden phase: the pre-solve sublanguage saturation re-run on the
  post-wiring graph. Skipping the re-run (`--cfl-presolve-once`) is
  faster AND strictly tighter — it attributes the task-#43
  incremental divergence (−504 pairs, all at opt_pre_handler) to
  pool-smear manufactured by that re-run's coarsening. VALIDATED
  (2026-08-16): at fs41 the flag is byte-identical to the EAGER pin
  (the smear family is a P=13 residue-collision artifact absent at
  P=41) and 1.55x (fs41 mono 1h49m -> 1h11m); at fs13 it is strictly
  tighter (-504, all opt_pre_handler) and faster. fs INCREMENTAL is
  thereby unblocked: incremental + presolve-once is byte-identical
  to the presolve-once scratch pin at km fs13 (150,238) at 13m52s —
  the #43 divergence is closed by attribution, not by workaround.

### 3.2 Data structures and memory

- **Dual-representation fact sets.** Sorted SmallVector below 128
  entries, dense bit plane above; every set operation has both-mode
  paths, and dense buffers widen lazily as the root universe grows.
- **COW plane interning** (#46, a997bc1): dense planes are shared
  copy-on-write via an intern sweep; pointer equality doubles as a
  content-equality certificate (interned skip on re-offers,
  adopt-on-full-arrival makes relay classes O(1)). The measured 60%
  row-duplication case. This economy shaped later work: two
  subsequent optimizations were rejected partly because they would
  destroy adopt fast paths.
- **Cluster-mark join fast path** (#48, 32d8793): profile-guided —
  99.8% of join lookups were redundant cold hash probes; a monotone
  mark plane per (cluster, shift) turned 39.94M lookups into 96k at
  km FI. Conservative by construction: marks may be lost (merges),
  never wrong. Replaced a planned parallel-exchange design that
  profiling capped at 1.4x.
- **Batch-mode grid-space marks** (d105585): marks keyed in global
  rid space survive across batches and rounds; the o-space backlog is
  imaged once per sweep by a word-shifted copy, valid for any rid
  base. Fixed the batch-local dense-promotion sizing bug that had
  gated workers off the fast path entirely. Batched fs13 2.75x.
- **Fused delta-OR kernels + self-contained BitPlane** (c61ae11).
  The general add path cost ~16 plane streams per effective OR; the
  dense common case now runs two fused loops (delta with inline
  any/popcount; one OR loop into all targets). Dense storage moved
  off llvm::BitVector (private word storage, unstable internal API)
  onto an in-repo ~150-line BitPlane mirroring exactly the consumed
  API surface with honest mutable word access. a-prop and f-prop
  each ~3x; fs41 1.41x further.
- **Small hygiene with outsized effect**: per-thread scratch FactSets
  reused across the hot paths (no allocation in the pop loop);
  edge/cell lists compacted against union-find staleness at pop time
  (`compactLists`); boost flat hash containers for the hot maps —
  with the measured counter-example that SHARDING the cluster map
  tripled probe cost by scattering the hot header across cache lines;
  group-indexed arrays with touched-lists where reused hash maps'
  clear() would scan grown capacity (the bundle-epoch grind).

### 3.3 Process and I/O engineering

- **Fork/CoW batch workers** (#41, 00cf6b0/311e630): process-parallel
  batches share the graph and quotient copy-on-write; workers drain
  single-threaded, stream effectual events (key inserts, merges) and
  harvest bits through scratch files, and _exit without LLVM
  teardown; the parent replays event streams (Jacobi rounds, same
  closure — worker interleaving lives below the `batched_exact`
  abstraction). 3.8x over sequential batches then; 9.2x core
  utilization at fs41 today. This is also the concurrency stance:
  no lock-based threading was added anywhere in this work — the
  solve is sequential or share-nothing process-parallel; the only
  locks are the pre-existing per-class spinlocks of the optional
  threaded wave mode.
- **Per-worker thread pools** (0e841c2) claim their core share
  post-fork; the parent's pool is torn down to one thread so forks
  stay safe.
- **Batch-local fact universes** (#41, b5e560c): worker dense planes
  are sized to the batch (K bits), not the global root count — the
  width compression that later subsumed origin bundles.
- **Plane spill/restore** (#42, 51a85ef/6509dbb): batches serialize
  their fixpoints and later rounds restore + drain only the
  touch-log-window delta (offload over recompute), with frozen batch
  bounds, per-batch cursors, and skip-save for unchanged restores.
- **Streaming compression** (06aa986/175d496): raw kernel spill is
  ~8.7GB/batch (~300GB projected); zstd-streamed spill compresses
  ~600x (replicated fragment fact-sets are near-identical byte
  blocks). The restore is a two-pass re-decompression instead of a
  buffered load, after a buffered restore doubled the fattest batch
  on top of the 43GB floor and blew the address-space cap 2.7 hours
  into a 10.5-hour kernel run.
- **Memory guarding** (34722fd): an RSS watchdog replaced RLIMIT_AS
  as the default guard — address-space caps killed runs whose
  resident set never left the floor (glibc arena address reservation;
  operationally paired with MALLOC_ARENA_MAX=2). Kernel-scale runs
  ship in a runtime container with spill on the container disk
  (0b51673).
- **Determinism hygiene**: GUID-keyed self-filtering removed
  binary-dependent dump nondeterminism; answer-set pins live outside
  git history (sha256 in stats files) after repository size forced a
  history strip.

## 4. Negative results (kept, with measurements)

Documented falsifications are part of the method; each has an in-code
tombstone or design-doc post-mortem:

- **Plane-occupancy skip masks**: targeted a phase measured at 0.005%
  of cycles; byte-identical and wall-flat; reverted. (93% of planes
  are live at pop — fs plane cost is real work.)
- **Stage-2 root bundling (#47)**: fs fact mass is exact roots times
  facts, non-bundleable by construction at that design point.
- **Origin-bundle epochs**: exactness fully machine-checked and
  validated at km scale (byte-identical through two epochs plus
  expansion), but the economics fail structurally — epochs cost
  O(live mass) while co-travel forms late, and the compression dies
  at expansion and from-scratch rebuilds. Parked default-off; the
  decider showed batching subsumes the width lever (K-wide batch
  planes) with no epoch cost.
- **Merge-block fusion**: byte-identical, wall-flat, merge cycles
  +14% — the merge bucket's mass is re-offer/adopt-path traffic, not
  the move arithmetic. Reverted with tombstone.
- **Slab/chunked plane layouts**: falsified pre-build by measurement
  (IPC 2.76 = compute-bound, no locality debt; streamed deltas
  already 92.7% zero-word-skipped).
- Earlier vintages of the same discipline: delta-precise merge
  re-offers (streams the heavy plane 3-4 extra times), sharded
  cluster maps (tripled hot probe cost), deliberate merge keeper
  policies (union-by-rank wins), Lemma-3.4 small-to-large transfer
  (does not apply when merges carry plane payloads).

## 5. Status at time of writing

- fs41 batched + presolve-once: 38m11s, byte-identical (149,791) —
  the recommended fs41 mode; full-session arc 4h13m -> 38m (6.6x).
- fs41 incremental + presolve-once: OOM on the 62GB machine (the
  retained cross-iteration fixpoint needs ~55-65GB at fs41) — a
  machine constraint, not a method failure; viable on the big
  machine for the kernel-scale HEAD re-run, which now inherits the
  full stack.
- Default policy for --cfl-presolve-once: byte-identical at fs41,
  answer-changing (tighter) at fs13 — stays opt-in until pins are
  re-cut.
