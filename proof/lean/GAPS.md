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
