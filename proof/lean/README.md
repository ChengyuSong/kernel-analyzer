# Lean Scaffold: Compositional CFL Soundness

This is a minimal Lean 4 project that mechanically checks a core soundness theorem schema for compositional CFL analysis.

## What is formalized

- A small labeled-graph model (`Graph`, `LEdge`, `Label`)
- A simplified CFL-style reachability judgment (`Reach`)
- A graph-homomorphism/simulation notion (`GraphHom`)
- Explicit boundary-symbol categories:
  - core: `func`, `arg`, `ret`, `vararg`, `glob`, `icall`
  - precision extras: `icallret`, `lret`, `gptr`, `gderef`
- Iterative compositional augmentation model (`IterStep`, `iterClosure`) for
  summary-edge fixed-point solving
- A checked theorem:
  - `reach_map`: reachability is preserved under graph simulation
  - `reach_mono`: reachability is monotone under edge inclusion
  - `compositional_sound`: monolithic reachability implies composed reachability, given a simulation map `q`
  - `compositional_sound_iterative`: adding edges after one-shot composition remains sound
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
