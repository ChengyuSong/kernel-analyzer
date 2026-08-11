# Lean Scaffold: CFL Callgraph Soundness

This is a minimal Lean 4 project that mechanically checks core soundness
theorem schemas for the two analysis pipelines:

- `CompositionalCFL/Core.lean` — the compositional (per-TU compress +
  boundary merge + iterative closure) pipeline over the field-insensitive
  grammar (Feb 2026).
- `CompositionalCFL/FlowsTo.lean` — the flows-to (ORCFL) solver over the
  shift-indexed field grammar (Jul 2026, branch `orcfl`), now the primary
  scaling path.

## What is formalized (flows-to, `FlowsTo.lean`)

- Shift monoid with absorbing `⊤` (`ShiftMonoid`, `Shift`, `shiftComp`);
  exact-`Nat`-offset instance (`natShifts`); the production `Z_P` bucketing
  is a monoid quotient of it (formalization pending, gap F5)
- Declarative shift-indexed flows-to derivations (`FDeriv`):
  value flow with net shift (`a`/`f r`/`fx` steps, memory hops through
  aliased cells), and cell aliasing by exact-shift join (V) or `⊤` (VX)
- Checked theorems:
  - `fderiv_mono`: derivability monotone under edge growth — covers the
    outer icall fixpoint (wiring only adds edges)
  - `fderiv_map` / `fderiv_quotient`: derivability preserved under node
    quotients — covers presolve merges, union-find cell merges, and the
    dynamic a-SCC collapse (soundness direction)
  - `solver_complete`: the minted-root solver abstraction (`SolverModel`)
    derives every grammar-derivable fact and alias GIVEN the `origins_minted`
    invariant (every node reached by some minted root). The 2026-07-13
    minting bug is precisely an `origins_minted` violation.
  - `answers_complete`: icall answers (shift 0 or ⊤ at the fptr) are found
    whenever function nodes are minted and `origins_minted` holds

See the "Flows-to (ORCFL) model gaps" section of `GAPS.md` for what remains
assumed (`origins_minted` discharge from the minting criterion — now checked per run by certificate C7 — SCC-collapse
precision-neutrality, bridge provenance, `Z_P` quotient, FactSet refinement,
target filters).

## What is formalized (compositional, `Core.lean`)

- A small labeled-graph model (`Graph`, `LEdge`, `Label`)
- A simplified CFL-style reachability judgment (`Reach`)
- A graph-homomorphism/simulation notion (`GraphHom`)
- Explicit boundary-symbol categories:
  - core: `func`, `arg`, `ret`, `vararg`, `glob`, `icall`,
    `larg`, `lret`, `lvararg`, `icallarg`, `icallret`
  - precision extras: `gptr`, `gderef`
- Iterative compositional augmentation model (`IterStep`, `iterClosure`) for
  summary-edge fixed-point solving
- Boundary pinning model (`pinBoundaryNodes`) for keeping edge-isolated
  boundary nodes materialized through compression
- Assign-pair summary-rule schema (`assignBridgeRule`) for compositional
  icall-arg propagation (`icallarg -> arg/larg/vararg/lvararg`)
- A checked theorem:
  - `reach_map`: reachability is preserved under graph simulation
  - `reach_mono`: reachability is monotone under edge inclusion
  - `compositional_sound`: monolithic reachability implies composed reachability, given a simulation map `q`
  - `compositional_sound_iterative`: adding edges after one-shot composition remains sound
  - `compositional_sound_with_pinned_boundaries`: soundness preserved when
    boundary-seed self-edges are added before export/composition
  - `compositional_sound_assignBridge_iterClosure`: iterative soundness
    specialized to `a/-a` assign-pair summary wiring
  - `compositional_sound_two_stage_iterClosure`: per-TU quotient + boundary merge + global iterative closure remains sound

The key idea is reusable: prove your concrete pipeline induces `GraphHom q Gmono Gcomp`, then soundness follows immediately.

## Files

- `CompositionalCFL/Core.lean`: definitions + theorems
- `CompositionalCFL.lean`: library entrypoint
- `GAPS.md`: tracked gaps between Lean model and C++ implementation
- `lakefile.lean`, `lean-toolchain`: Lean project config

Cross-reference:
- implementation-side discussion:
  [`docs/compositional-cfl-analysis.md`](../../docs/compositional-cfl-analysis.md)

## Run

From `proof/lean`:

```bash
lake build
lake build CompositionalCFL
```

## How to extend toward your full analysis

1. Strengthen `Reach` to match your exact grammar and solver rules.
2. Model per-TU V-SCC quotient explicitly and prove edge simulation into each TU quotient.
3. Model boundary-symbol union-find composition and prove it preserves cross-TU edge steps.
4. Instantiate `SummaryRule` with your concrete summary-edge rule
   (e.g. bridges such as `ret(target) -> icallret(callsite)`), prove it is monotone,
   and build an `IterStep` via `mkSummaryIterStep`.
5. Compose these lemmas to discharge `hSim` for the real `q`.

At that point, `compositional_sound`/`compositional_sound_iterative` become a fully mechanized proof schema for your implemented construction.

## Review-response theorems (2026-08-11)

- `sderiv_sound_fderiv` / `sderiv_iff_fderiv` — least-closure
  soundness + two-sided equivalence with the rooted grammar at exact
  seeds (the converse direction the review noted was missing).
- `pol_solver_complete` / `pol_answers_complete` — per-root seed
  policy (exact vs wildcard): the surgical minting mode's abstraction
  theorem; widened origins report every grammar answer at ⊤.
- `ShiftHom` / `fderiv_shift_hom` / `intShifts` / `zpShifts` /
  `natToZp` — residue abstraction as a proved homomorphism transfer;
  signed ground truth is `intShifts`, the signed→Z_P instance is the
  remaining item (GAPS).
- `Core.lean` `boundary_sound` corrected to same-present-symbol.
