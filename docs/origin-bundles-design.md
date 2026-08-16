# Origin-Equivalence Bundles: Design and Proof Obligations

Status: DESIGN (2026-08-15). Gate 0 (fs-mode co-travel sizing) in
flight. Nothing implemented; this document is the reviewable artifact.

## 1. Objective and honest sizing

Bundle = a set of root origins represented by ONE fact id wherever
they co-travel (identical (class, shift) incidence). Measured at km
FI (`--cfl-cotravel-stats`, HEAD 2026-08-14): 53,794 active roots →
33,358 distinct incidence columns, max bundle 17,811 (the hub
cohort), fact-mass compression 3.21x (178.9M → 55.8M).

**Sizing correction (post-cell-major).** The old "≈3x fs wall"
estimate predates the join restructure and conflates fact-mass
compression with wall time. After f13f8d6/d105585 the fs profile is
a-prop 27.7% + f-prop 35.1% + join 33.1% (km fs41), and the dominant
costs are WIDTH-BOUND: dense-plane word streams (addBits ORs, subset
scans, merge plane moves) scale with the rid universe width, not the
set-bit count. Bundling with rid-space compaction cuts width by the
root ratio — 53,794/33,358 ≈ **1.61x at km FI** — not 3.21x. Sparse
structures (cluster registry population, sparse rows, sweepElems,
merge payload popcounts) do scale with fact mass and see the 3.21x.
Blended expectation at km: **~1.4–1.6x fs wall**. Gate 0 re-measures
both ratios under fs13, where the X plane and per-shift rows may
change the picture in either direction; kernel-scale ratios are
plausibly better (larger hub cohort share) but unmeasured.

Kill criterion: if Gate 0's fs root ratio is < ~1.3x, the width lever
is too small to justify the rid-renumbering machinery — stop and
re-rank against channels.

## 2. Semantic foundation: the coupling lemma

The historical fear (task #17 inversion: heap-identity SPLITTING
regressed, so identity structure is delicate) was that sharing one
fact id across origins lets stores reachable from one origin smear
into loads of another. The following code-anchored lemma says the
exact solver ALREADY forces that sharing for co-traveling origins,
so bundling shares nothing new:

**L1 (coupling through shared cells).** In `joinCluster(cell, o, s)`
the cluster of key (o, s) is a union-find CLASS: the first join sets
`clusterRep[(o,s)] = find(cell)`, later joins `merge` the cell's
class into it. Therefore one cell class c joining two keys (o1, s)
and (o2, s) merges the two clusters through c. If rows(o1) = rows(o2)
at a quiescent point (same (class, shift) incidence), both origins
joined exactly the same cell classes, so either neither has a
cluster, or their clusters are ONE class already. Their "memory
nodes" are already unified in the exact per-origin solve; and since
union-find never un-merges, every future join by either origin lands
in that shared class in the per-origin world too.

Consequences:
- Bundle-level joins (`joinCluster(cell, B, s)`) perform literally
  the same merges the member-level joins would; no precision is lost
  and none is gained — EXACT, not just sound.
- Split-on-divergence (if ever needed) is exact with cluster-ref
  INHERITANCE: children keep pointing at the shared cluster class,
  because per-origin behavior after the divergence point also keeps
  feeding that same class. No cluster copying, no un-merging.
- The lemma is assertable at bundling time: for every candidate
  bundle, all members' `clusterFind((o,s))` must be equal or all
  absent, per shift. This assertion is the runtime check of the
  entire theory and MUST be in the implementation (no silent
  fallback; a violation falsifies the design, not the input).

## 3. Structural facts that constrain the mechanics

1. **Roots are classes.** Each root rid is minted for a distinct
   class (`mintRoot(rep)`), so no two origins are born identical:
   co-travel emerges MID-SOLVE (the cohort's seed classes merge into
   the hub). Seed-time bundling captures nothing; bundles must form
   at in-solve quiescent points ("epochs").
2. **fs wiring iterations are from-scratch.** Under field
   sensitivity, incremental is refused: each of the ~5 outer
   iterations rebuilds and re-solves; union-find and planes do NOT
   persist across iterations. So cross-iteration "predictive"
   bundling has no stable class space to predict into; bundles form
   fresh within each iteration's solve. (Iteration 1 is the fs41
   monster — 54% of solve wall — and is fully in scope for
   within-iteration epochs.)
3. **Epochs need not be quiescent (audit result).** The injection
   audit (Stage 1, DONE 2026-08-15) found `addFact` reaches planes
   from exactly three sites — initial seeding, new-rid incremental
   minting, batch seeding — all of which seed a rid at its OWN class
   at its birth. No mid-solve injection ever targets an existing
   rid. Therefore no solver rule distinguishes two rids except the
   excluded per-rid mechanisms (§3.5), and two origins with equal
   FULL per-rid state — rows across R/RB/dirty/jdirty/dirtyBr AND
   joined, plus equal-or-absent cluster assignment (L1 assertion) —
   have identical futures from ANY point, not just quiescent ones.
   V1 epochs are therefore periodic drain checkpoints (every X pops)
   hashing full-state rows; mono needs no new synchronization and no
   waiting for rounds. Batch-round and lazy-round boundaries remain
   convenient (smaller state to hash: delta planes empty there).
4. **Width cut requires compaction.** Universe ids are monotone;
   zeroing member columns leaves dead width. The epoch pass must
   RENUMBER the rid space (members retired, bundle ids allocated,
   survivors permuted) and remap every rid-indexed structure:
   R/RB/dirty/jdirty/dirtyBr rows are (class, shift)-indexed with
   rid BITS — one streaming rewrite pass over fact mass;
   `clusterRep`/`shiftKeysOf` keys; `joined` planes remapped in the
   same pass; `cellJoined` marks may simply be DROPPED (conservative
   re-probe, cheap re-warm — same policy as merge mark loss);
   harvest (`fptrAcc`), ICALL dump, and instruments expand bundle
   bits to leaf rids through the bundle table.
5. **Per-rid special cases are excluded, not split (v1) — audit
   DONE.** Complete list of per-rid mechanisms that survive past
   seeding: (a) prot machinery (`protRid`/`prot[o]` per-rid cell
   state in joinCluster) — EXCLUDE prot rids from bundling;
   (b) `rootRodata` probe and sink-ablate reroutes — measurement
   flags, REFUSE the flag combination with bundling (they already
   disable the join fast path); (c) `shiftKeysOf`/VX bridging —
   per-key, works at bundle-node granularity unchanged, covered by
   the L1 assertion across all shifts including X; (d) `mergeWitness`
   (root-relevance instrument) — expand or refuse under flag;
   (e) harvest/dump/type-tally — leaf expansion at read time.
   Nexus/rodata SEED gating only affects birth shift (pre-bundle).
   Summaries, INVOKE/CHAINREG atoms plant graph structure pre-solve.
   `wireIncremental` is FI-only (fs is from-scratch). Consequently
   the split protocol is never exercised in v1 and ships only if a
   future mechanism injects into existing rids (v2: split with
   cluster-ref inheritance, exact per L1).

## 4. Epoch pass (v1 sketch)

At an epoch (drain checkpoint, sequential):
1. Full-state row-hash all roots — R/RB/dirty/jdirty/dirtyBr/joined
   contributions (reuse the cotravel `colHash` machinery, 128-bit
   mix), group, then VERIFY equality exactly within groups
   (collision ⇒ union ⇒ over-approx: sound but not byte-identical —
   we promise byte-identical, so verify and assert).
2. Filter by the exclusion list and a minimum bundle size (≥ 4?
   measure); assert L1 cluster equality per surviving bundle.
3. Build the renumbering map (bundle table: bundle id → member leaf
   list; survivors compacted), rewrite all planes in one streaming
   pass, remap cluster keys, drop cellJoined, expand nothing (answers
   only materialize at harvest).
4. Continue the drain. Later epochs may coarsen further (bundles of
   bundles are just bundles — the table is a forest).

Cost bound: one fact-mass stream per epoch (≈ one merge-heavy wave);
2–3 epochs per iteration expected (after the first A-round, after
catch-up). If epoch cost shows up in SolverProf, cap epochs at 1.

## 5. Proof plan (Lean, proof/lean WDeriv infrastructure)

- **T2 / coupling**: in the witness-table model, equal rows at a
  quiescent table state imply equal cluster assignment (formalizes
  L1; the merge-through-shared-cell step is a two-line consequence
  of the join rule's union-find semantics in the model).
- **T1 / bundle_exact**: a quotient q on origins that identifies
  only row-equal origins at a quiescent state, with no subsequent
  rule distinguishing members (the exclusion side condition),
  yields a bundled closure whose leaf expansion equals the eager
  closure. Structure mirrors `batched_exact` (sound + closed table ⇒
  union = eager closure); the quotient plays the role the batch
  partition played.
- **T3 / epoch confluence**: coarsen-at-quiescence then continue =
  eager fixpoint. Reuses the `wderiv_restore` spill-confluence
  skeleton (an epoch is a restore with a renamed universe).
- GAPS.md entries for what stays engineering-verified only: the
  renumbering pass fidelity (plane rewrite = bijection on facts),
  harvest expansion, instrument expansion.

Order: T2 first (small, and its runtime assertion ships in v1
regardless), then T1, then T3. No `sorry` enters the tree; anything
unproven stays in GAPS.md and the flag stays default-off until T1+T3
close.

## 6. Cheap sibling worth measuring first: dynamic a-SCC merge

The cotravel instrument already measures the ROW-side dual: classes
mutually reachable over the post-merge a-graph have provably equal
fact planes at fixpoint and are mergeable with the EXISTING merge()
machinery (HVN/offline-variable-substitution analog — no new
representation, no renumbering, much smaller proof: SCC ⇒ equal
planes ⇒ merge is exact). If Gate 0 shows a large "dynamic a-SCC"
count under fs, a Stage-0.5 experiment (merge nontrivial a-SCCs at
the same epochs) may capture a chunk of the plane-duplication win
for a fraction of the engineering. Bundles (columns) and a-SCC
merges (rows) compose.

## 7. Stages and gates

- **Gate 0** (PASSED 2026-08-15, /data/csong/tmp/km-fs13-cotravel.log,
  answers = pin 150,742): km fs13 — active roots 73,713 → 37,748
  distinct columns, **root ratio 1.95x** (> FI's 1.61x), max bundle
  31,771 (43% of active roots = the hub cohort is proportionally
  LARGER under fs), fact compression **4.84x** (7.08B → 1.46B).
  Width and mass levers both clear the kill line with margin.
  a-SCC census: 22 nontrivial SCCs, 570 collapsible classes, 2,642
  intra-SCC a-edges of 75,850 — Stage-0.5 (dynamic a-SCC merge) is
  NOT worth building; the row-side sharing is already captured by
  #46 plane interning. Bundles are the lever.
- **Stage 1** (DONE 2026-08-15): `addFact`/per-rid injection audit →
  exclusion list is prot rids + refused measurement-flag combos;
  no split protocol needed in v1 (§3.5). Remaining piece: an
  instrument counting bundleable mass under exclusions.
- **Stage 2**: T2 proof + epoch coarsener behind
  `--cfl-origin-bundles` (default off), mono fs first. Assertions:
  L1 cluster equality, row verification, renumber bijection count.
- **Gate 2** (RUN 2026-08-15, VERDICT: **WALL FAIL — PARKED**):
  km fs13 with `--cfl-origin-bundles` is BYTE-IDENTICAL (150,742;
  2 epochs folding 74,891 → 48,910 ids = 1.53x width, iteration-0
  resolution identical, every L1/presence assertion silent — the
  exactness theory and the whole epoch/expansion pipeline are
  validated at km scale) but the wall is 157m54s vs 32m27s: each
  epoch's refine+remap streams all six plane families (440s/816s at
  ~0.2/0.4B mass; expansion 425s) against 230s drains, and the
  benefit dies at every drain-end expansion and from-scratch
  iteration rebuild. Two implementation lessons are recorded in the
  code: the partition-refinement pre-split-size snapshot (the first
  L1 assertion catch was an under-split bug, not theory) and the
  MEMOIZED-state discovery — row equality does NOT imply cluster
  equality at a checkpoint (merge's joined-intersection erases row
  evidence the registry keeps), so the epoch test must refine on
  (presence, cluster class) per shift. The second L1 firing caught
  exactly this; both are now part of the epoch test.
- **Post-mortem (why the economics fail structurally at km)**: the
  width lever pays on dense-plane streaming, but harvesting it costs
  O(live mass) per epoch while co-travel only forms LATE in each
  drain (0.67% foldable at 40k of 265k pops), the compressed state
  dies at expansion, and fs iterations rebuild from scratch. At
  kernel scale the question is moot: kernel fs runs are BATCHED, and
  batch-local planes (K=4000 wide) are a stronger width compression
  than bundles can reach. Decision experiment: fs41 batched vs mono
  — RESULT (2026-08-15): batched 108m vs mono 155m, byte-identical
  (149,791), with 8 workers at 9.2x core utilization. Batching WINS
  at both fs13 and fs41: it subsumes the width lever (K=4000-wide
  batch planes) with better economics and no epoch cost. BUNDLES
  CLOSED. Practical guidance: batched is the recommended fs mode.
- **Stage 3** (only if a future config needs it): epoch cost would
  have to drop ~20x (single-pass hashing + word-level remap have no
  obvious path there) or bundles would need to survive expansion
  (contradicts the v1 no-consumer-changes architecture).
