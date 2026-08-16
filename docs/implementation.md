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

The 2026-08 sequence took km fs41 from 4h13m to 1h32m (2.76x) and km
fs13 to 23m; each step's mechanism and measured effect:

- **COW plane interning** (earlier, #46): dense fact planes are
  shared copy-on-write; pointer equality doubles as a content-equality
  certificate (interned skip on re-offers, adopt-on-full-arrival for
  relay classes). This economy shaped later work: two subsequent
  optimizations were rejected partly because they would destroy adopt
  fast paths.
- **Cell-major join sweep.** The join backlog filter did a ~350-cycle
  probe per (fact, cell) visit with 99.98% proven no-ops (9.0B skips
  vs 1.8M real joins — merge re-offers re-confirming absorbed
  planes). Inverting fact-major to cell-major answers the whole
  backlog per cell at word level: a read-only subset scan (`subsetOf`,
  with the interned pointer fast path) certifies "cluster already
  absorbed all of this", a word-ANDN materializes the residual, and
  per-fact work remains only for first joins. Join phase 69.5% → 33.1%
  of pop cycles; fs41 1.63x.
- **Batch-mode join fast path.** Batch workers previously had no join
  marks at all (a batch-local-universe overflow — root-caused to
  dense promotion sizing — had gated them off). Marks moved to global
  grid space (valid across batches and rounds: the cluster registry
  is global and clusters only grow), with the o-space backlog imaged
  once per sweep by a word-shifted copy, valid for any rid base.
  Batched fs13 2.75x; batched == mono re-pinned byte-identical.
- **Fused delta-OR kernels + self-contained BitPlane.** The general
  add path cost ~16 plane streams per effective OR (copy, subtract,
  emptiness scan, four separate unions each with its own COW check,
  count). The dense common case now runs two fused loops (delta with
  inline any/popcount; one OR loop into all target planes). Dense
  storage moved from llvm::BitVector (private word storage, unstable
  internal API) to an in-repo ~150-line BitPlane mirroring exactly
  the consumed API surface with honest mutable word access. a-prop
  and f-prop each ~3x; fs41 1.41x further; FI to 3m55s.
- **Concurrency stance.** No lock-based threading was added anywhere:
  the solve is sequential or share-nothing process-parallel (forked
  batch workers, Jacobi rounds replayed by the parent; 9.2x core
  utilization at fs41). The only locks are the pre-existing per-class
  spinlocks of the optional threaded wave mode.
- **Wall decomposition beats micro-optimization.** After the kernel
  work, hardware counters (IPC 2.76, LLC misses ~1.4% of cycles)
  showed the solver at its compute floor — and timestamp decomposition
  exposed that 56% of the remaining fs41 wall was a single hidden
  phase: the pre-solve sublanguage saturation re-run on the
  post-wiring graph (a one-time giant-SCC discovery). Skipping the
  re-run (`--cfl-presolve-once`) is faster AND strictly tighter — it
  attributes the long-standing task-#43 incremental divergence (−504
  pairs, all at opt_pre_handler) to pool-smear manufactured by that
  re-run's coarsening, not to incremental solving. Validation of the
  smear-free pin and the unblocked fs-incremental combo is in flight.

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

## 5. Pending at time of writing

- fs41 `--cfl-presolve-once` A/B (wall + smear-family delta check).
- fs-incremental + presolve-once byte-identity against the
  presolve-once scratch pin (micro gate already passes; would
  collapse the 5x from-scratch iteration structure under fs).
- Kernel-scale HEAD re-run inheriting the full optimization stack.
