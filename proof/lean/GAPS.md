# Lean vs Implementation Gaps

This file tracks the major gaps between the Lean formal model in `proof/lean`
and the current C++ implementation in `src/lib/CallGraph.cc`.

Cross-links:
- Implementation doc section:
  [`docs/compositional-cfl-analysis.md`](../../docs/compositional-cfl-analysis.md)
  under "Current mechanization gaps (Lean model vs implementation)"
- Lean overview: [`README.md`](README.md)

## Major gaps

1. Obligations are assumed, not discharged from implementation code.
- Lean proves soundness once graph-homomorphism obligations are provided.
- We do not yet prove that `compressConstraintGraph` + `runCompositionalSolve`
  construct those obligations for all inputs.

2. Iteration model mismatch.
- Lean models unbounded fixed-point closure (`iterClosure`).
- Implementation uses explicit caps:
  - per-TU: `kMaxPerTUIterations = 32`
  - composed/global: `kMaxCompIterations = 8`
- With finite monotone edge growth, convergence is guaranteed without caps, so
  caps are defensive and can stop before the true fixed point.

3. Compression model mismatch.
- Lean quotient/composition is abstract edge remapping.
- Implementation drops SCC self-loops during remap and then re-adds terminal
  `a/-a/d/-d` loops for multi-node SCCs.
- A proof that this concrete construction refines the abstract model is pending.

4. Boundary completeness is assumed in Lean.
- Lean assumes all cross-TU-relevant boundary facts are exported.
- The Lean kind set now includes implementation-required classes
  (`func/arg/ret/vararg/glob/icall/larg/lret/lvararg/icallarg/icallret`),
  but export completeness is still an assumption.
- Lean now models boundary-node pinning (`pinBoundaryNodes`) and proves
  soundness preservation under seed self-edge addition, matching the
  edge-isolated-boundary fix direction in implementation.
- Implementation depends on extraction paths (metadata and pattern-based
  discovery), plus cache sanity checks.
- Completeness of these extraction paths is not formally proved.

5. Summary bridge discovery is abstract in Lean.
- Lean models assign-pair summary generation (`assignBridgeRule`) from an
  abstract monotone bridge relation.
- Implementation computes concrete bridges from resolved indirect-call targets,
  `icallarg` symbols, and callee arg/vararg symbols.
- A refinement proof connecting implementation bridge extraction to the Lean
  bridge predicate is pending.

6. Target filters are not yet formalized.
- Implementation applies `isCompatible` and field-store filtering
  (`fieldFilterAccepts`).
- Lean currently has no model/proof that these filters are conservative with
  respect to monolithic truth.

7. Allocator promotion logic is out of model.
- `findCustomAllocators` and `findCustomAllocatorsComposed` mutate allocator
  sets and may rewrite call-related edges in monolithic mode.
- Lean does not model this state transition or prove its preservation properties.

8. Solver implementation is trusted.
- Lean reasons over declarative reachability.
- `SolverFWGramParallel` is treated as an oracle in the end-to-end story.
- A refinement proof (solver output implies declarative `Reach`) is missing.

9. Function-identity canonicalization is not modeled.
- Implementation uses GUID-based identity in places where pointer identity can
  diverge across declaration/definition forms (e.g., compositional func-node
  collection and field-store correlation).
- Lean currently abstracts over node/function identity and does not model this
  declaration-vs-definition canonicalization step.

## Notes

These gaps do not invalidate the current Lean schema proofs. They define the
work needed to claim a full machine-checked proof for the exact production
pipeline.

---

# Flows-to (ORCFL) model gaps — added 2026-07-14

The primary solver is now `runFlowsToResolution` (branch `orcfl`), modeled in
`CompositionalCFL/FlowsTo.lean`. Machine-checked so far:

- `fderiv_mono`: derivability monotone under edge growth — covers the outer
  fixpoint (resolve icalls → `handleCall` wiring → re-solve only adds edges).
- `fderiv_map` / `fderiv_quotient`: derivability preserved under node
  quotients — covers presolve copy/field merges, cell-cluster union-find
  merges, and the dynamic a-SCC collapse (soundness direction).
- `solver_complete`: given the closure rules and the `coverage` invariant
  (every node reached by some minted root), the solver derives every
  grammar-derivable flow and alias.
- `answers_complete`: icall answers (shift zero or ⊤ at the fptr) are found
  whenever function nodes are minted and coverage holds.
- `sderiv_catchup` / `catchup_answers_complete`: staged (lazy-mint)
  solving with a final catch-up to full minting equals the from-scratch
  closure — exactness of task #21's catch-up round.
- `answer_not_derivable_restricted`: restricted minting genuinely loses
  answers (counterexample), so `origins_minted` cannot be weakened
  without a sufficiency proof for the restricted set (open, F11).

## Flows-to gaps

F1. [REVISED 2026-07-14] The grammar is now ROOTED at origins
(`FDeriv`'s `origin` parameter), and the solver hypothesis is
`origins_minted : origin ⊆ minted` — dischargeable, since the
implementation mints every origin-bearing class. The July-13 minting
bug is a violation of exactly this hypothesis. Remaining code-level
gap: the correspondence between Lean origins and the implemented
criterion (canonicalClassMembers sweep over alloca / global /
alloc-site values) is informal. Note the rooting DEFINES a semantic
difference from pairwise saturation: saturation admits unrooted valley
apexes (φ-cycles, entry-less store/load loops = undef values), so
flows-to ⊆ saturation on such patterns is principled, not a bug —
exact saturation parity is the wrong validation target.

F2. a-SCC collapse precision-neutrality (the converse of `fderiv_quotient`)
is unproved. Soundness needs only the proved direction; the claim that
collapsing mutually shift-preserving-reachable classes loses no precision
rests on the cycle-insertion argument, checked only empirically
(identical per-icall results on libpng/harfbuzz).

F3. [DOWNGRADED 2026-07-14] Union-find cluster transitivity was
suspected to over-approximate the grammar's per-witness M; writing the
model shows it is FACT-EQUIVALENT: `flow_m` steps chain across aliased
cells, so fact sets equalize transitively in the grammar too — the
solver never consumes the alias judgment itself, only the fact flow.
Residual: cluster merges also unify cell lists and edges of the merged
content classes; believed equivalent by the same chaining argument at
each pointer level, not formally checked. `ClusterTrans` runtime stats
(keys/cluster, transitive key-coalescing merges) monitor the coarsening
empirically (libpng FI: 506/546 keys in one cluster, resolution still
exactly matches saturation).

F4. VX bridge provenance (bridged facts never cross a second bridge) is
abstracted away: the model's `⊤` joins are unrestricted, i.e. at least as
permissive as the implementation. Completeness of the 1-bit provenance
restriction w.r.t. the grammar's value-step-laundering is checked only
empirically (phase-2 null result).

F5. The shift monoid instance proved is exact `Nat` offsets; the production
`Z_P` residue bucketing is a monoid quotient of it (sound abstraction),
but the quotient homomorphism is not yet formalized (needs `Fin P`
arithmetic or mathlib).

F6. `FactSet` (hybrid sparse/dense planes) is trusted as a set
implementation; no refinement proof.

F7. Iteration cap `--cfl-flows-to-max-iters` can stop before the outer
fixpoint; the implementation warns ([UNSOUND-RISK]) when it triggers.
Model assumes full closure.

F10. [ADDED 2026-07-14] The SolverModel closure fields (seed/step_a/
step_f/step_fx/step_mal) assume the worklist algorithm reaches
saturation — the delta/backlog machinery (jdirty refill on merge,
joined-plane intersection, merge-abort requeue) is where historical
solver bugs lived and is below the model. Practical discharge:
`--cfl-verify-closure` runs one full non-delta scan post-fixpoint and
asserts no rule fires (C0 backlogs drained, C1 a-prop, C2 f-prop,
C3 wildcard projection, C4 fact x cell joins, C5 bridge crossings) —
a per-run certificate of the model's assumption.

F11. [ADDED 2026-07-23, task #21] Lazy minting. Machine-checked:
`SDeriv` (least staged closure with a `base` fact relation),
`sderiv_catchup` (staging confluence: restricted drain → mint more →
continue = from-scratch closure over the final root set — the
exactness of the catch-up round, commit 446f35b),
`catchup_answers_complete` (end-to-end: staged solve with final
minting ⊇ origins finds every accepted answer), and
`answer_not_derivable_restricted` (necessity: a 5-node graph where
minting a strict subset of origins loses a grammar-derivable answer —
the July-23 whole-kernel deficit, -5737 pairs through tcp_ulp/9p ops
registration lists, is this shape at scale). OPEN: characterizing a
SUFFICIENT restricted root set. The implemented A-closure
(backward {a,f} + cell→owner hops on the live quotient, recomputed
per drain fixpoint) was conjectured sufficient by the first-missed-
join induction (scaling doc §2026-07-18) and is empirically REFUTED
at kernel scale — the induction breaks when a witness's consequence
path and another witness's occurrence path each need the other's
merge (cyclic dependence through circular list structure). The
catch-up round makes the conjecture moot for exactness; a formal
minimal-sufficient-set characterization would recover the ~3x
fact-mass savings without the catch-up's final-round cost.

F8. Target filters (`isCompatible`, `fieldFilterAccepts`) still unmodeled
(same as compositional gap 6): they subtract from the sound answer set,
so each rejection is a potential soundness hole. The planned
completeness-bit for `fieldFilterAccepts` and per-filter rejection
counters are prerequisites for retiring them; formalizing "filters reject
only grammar-underivable pairs" would discharge the gap.

F9. Edge-encoding completeness (IR construct coverage) is out of scope of
the model entirely: the July 2026 aggregate call-boundary bug lived here.
The systematic IR-construct census (task #13) is the practical mitigation.

## Batched solving (tasks #40-#42, added 2026-08-06)

Covered by the model (`WDeriv` section in `FlowsTo.lean`):
- `batched_exact`: sound + closed witness table ⇒ union of per-batch
  closures = eager closure (the #40/#41 exactness argument).
- `wderiv_restore`: spill restore-and-continue under a grown table equals
  the fresh drain (the #42 exactness argument).
- `wderiv_sound` is the per-round invariant that keeps the accumulated
  table sound from the empty start.

NOT covered (implementation-level, below the model's abstraction):
- The union-find/clusterRep/bridge machinery is modeled as the witness
  TABLE; that the recorded events regenerate exactly the join topology
  (worker replay, VX bridging) is unverified.
- The touch-window re-offer discipline (per-batch cursors, hot-class
  full re-offer, quiescent joined:=R∪RB) computes the `wderiv_restore`
  closure — the delta-completeness of that discipline is unverified.
- Batch-local universes (rid-blo bit translation) are a data-layout
  bijection, unverified.
- Round termination (monotone merges) is argued informally; the model
  takes the stable table as a hypothesis rather than constructing it.
