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

## Flows-to gaps

F1. Coverage is an assumption, not discharged from the minting code.
- The 2026-07-13 minting bug is the empirical violation: minting only
  `!hasIn` classes missed alloca classes captured by presolve merges.
- The current criterion (no-in-edge classes + origin-bearing classes +
  functions) is believed to imply coverage under the invariant "every
  source-SCC of the value graph contains an origin or is value-empty";
  that implication is not yet formalized.

F2. a-SCC collapse precision-neutrality (the converse of `fderiv_quotient`)
is unproved. Soundness needs only the proved direction; the claim that
collapsing mutually shift-preserving-reachable classes loses no precision
rests on the cycle-insertion argument, checked only empirically
(identical per-icall results on libpng/harfbuzz).

F3. The Lean `SAlias`/cluster model is non-transitive per join witness;
the implementation's union-find clusters are transitively closed, i.e.
coarser-or-equal. Fine for completeness (solver ⊇ grammar); the model does
not bound the implementation's over-approximation.

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

F8. Target filters (`isCompatible`, `fieldFilterAccepts`) still unmodeled
(same as compositional gap 6): they subtract from the sound answer set,
so each rejection is a potential soundness hole. The planned
completeness-bit for `fieldFilterAccepts` and per-filter rejection
counters are prerequisites for retiring them; formalizing "filters reject
only grammar-underivable pairs" would discharge the gap.

F9. Edge-encoding completeness (IR construct coverage) is out of scope of
the model entirely: the July 2026 aggregate call-boundary bug lived here.
The systematic IR-construct census (task #13) is the practical mitigation.
