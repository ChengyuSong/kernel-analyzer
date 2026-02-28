# TODO (Lean + C++ Soundness Link)

This tracks the remaining work to connect the mechanized Lean proof to the real C++ implementation.

## Current status

- Lean project scaffold exists under `proof/lean`.
- `Core.lean` now includes:
  - grammar-aligned `Reach` semantics (matching `DefaultP2Grammar` in `Global.h`),
  - generic simulation theorem (`reach_map`),
  - two-stage compositional soundness theorem,
  - explicit per-TU quotient and boundary-merge abstractions,
  - union-find-style boundary merge interface.
- Lean build succeeds with:
  - `export PATH="$HOME/.elan/bin:$PATH"`
  - `cd proof/lean && lake build`

## Goal

Prove that the **actual C++ pipeline** (`compressConstraintGraph` + `runCompositionalSolve`) refines the Lean model, then instantiate the existing soundness theorem for real runs.

## TODO1: Incremental `.cflcg` mismatch detection

Add strict cache-validity checks for compositional incremental runs so alias facts are not silently lost when program inputs evolve.

Status: completed (implemented in `CallGraph.cc` / `KAMain.cc` with new cache-policy flags).

1. Coverage checks
- [x] Record `covered_modules` in each `.cflcg` (stable module identifier set).
- [x] At compose time, require `union(covered_modules)` to equal current input module set.
- [x] Reject duplicates: a module must not be covered by multiple input `.cflcg` unless explicitly allowed.

2. Freshness checks
- [x] Record per-module IR hash (SHA256 of bitcode bytes) in `.cflcg`.
- [x] Recompute current module hashes at load time and reject stale entries.

3. Analysis compatibility checks
- [x] Record `analysis_key` in `.cflcg`:
  - grammar productions/signature,
  - required labels mapping,
  - relevant analysis flags (at least `global_dedup`, `local_alloca_summary`),
  - tool/schema version.
- [x] Fail closed on missing/invalid compatibility metadata in strict mode.

4. Runtime policy
- [x] Add strict mode (default for CI): hard fail on any missing/stale/incompatible module.
- [x] Optional repair mode: recompute missing/stale modules, then compose.
- [x] Emit explicit diagnostics listing: `missing`, `stale`, `duplicate`, `incompatible`.

5. Boundary sanity checks (defensive)
- [x] Validate boundary-symbol coverage expected from current IR against composed symbol space.
- [x] Treat missing required boundary classes (`func/arg/ret/vararg/glob/icall`) as cache inconsistency.

Implemented policy flags:
- `--cfl-cache-strict=<true|false>` (default `true`)
- `--cfl-cache-repair`
- `--cfl-cache-allow-duplicate-coverage`

## A. Translation-validation interface (C++ side)

1. Add dump mode flag(s)
- [ ] Add CLI flags to emit proof artifacts, e.g.:
  - `--lean-dump-dir <path>`
  - `--lean-dump-phase <per-tu|compose|all>`

2. Emit per-TU quotient artifacts in `compressConstraintGraph` path
- [ ] `tu_nodes.json`: node universe / IDs used in TU graph
- [ ] `tu_edges.json`: raw labeled TU edges
- [ ] `tu_qmap.json`: `orig_node -> scc_id`
- [ ] `tu_quot_edges.json`: quotient graph edges (after remap/dedup)

3. Emit composition artifacts in `runCompositionalSolve`
- [ ] `comp_symbols.json`: symbol -> occurrences
- [ ] `comp_unionfind.json`: parent/root mapping after unions
- [ ] `comp_merge_map.json`: unified/local node -> dense rep
- [ ] `comp_edges_in.json`: pre-compose quotient edges
- [ ] `comp_edges_out.json`: composed edges (after remap/dedup)

4. Determinism & checks
- [ ] Sort outputs deterministically.
- [ ] Emit counts/hashes for quick sanity checks.
- [ ] Include version field in each dump.

## B. Lean refinement layer

1. Add file(s)
- [ ] `proof/lean/CompositionalCFL/Refinement.lean`
- [ ] `proof/lean/CompositionalCFL/DumpModel.lean`

2. Define imported artifact model
- [ ] Lean structs for TU/composition dumps.
- [ ] Well-formedness predicates (`Valid*`).

3. Prove quotient obligations
- [ ] `ValidPerTUDump -> q_hom`.
- [ ] Show dumped quotient edges correspond to `quotientGraph` (modulo dedup/self-loop policy).

4. Prove merge obligations
- [ ] `ValidComposeDump -> merge_hom`.
- [ ] `ValidComposeDump -> same_symbol_same_rep`.

5. End-to-end instantiation
- [ ] Build theorem: `ValidDumps -> compositional_sound_two_stage`.

## C. Scope alignment details

1. Self-loops
- [ ] Decide exact Lean statement for dropped self-loops in quotient/composed edges.
- [ ] Prove dropping policy preserves `Reach` semantics used for soundness.

2. Node universes
- [ ] Clarify mapping between NF node IDs, dense IDs, unified IDs.
- [ ] Encode as explicit maps in Lean with domain constraints.

3. Symbols
- [ ] Freeze symbol schema assumptions in docs (`func/arg/ret/vararg/glob/icall`).
- [ ] Ensure scoped-name/GUID policy is reflected in validation predicates.

## D. Optional stronger results

1. Call-target layer
- [ ] Prove extraction from `V`-reachable function nodes is monotone/sound.
- [ ] Treat filters (`isCompatible`, field-store filter) with explicit assumptions.

2. Differential checks
- [ ] Add small-model exhaustive checker (outside Lean) to catch modeling mistakes early.

## E. Milestone plan (recommended)

1. M1: Dump schema + deterministic C++ artifact emission.
2. M2: Lean dump model + parsable sample artifacts.
3. M3: Prove `q_hom` and `merge_hom` from dumps.
4. M4: End-to-end theorem instantiation on real sample run.
5. M5: CI integration (`kanalyzer --lean-dump-dir ...` + `lake` check).

## Quick resume commands

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd proof/lean
lake build
```

## Notes

- Prefer translation validation over full C++ verification for tractability.
- Keep the trusted base explicit: parser/importer + dump-generation code.
