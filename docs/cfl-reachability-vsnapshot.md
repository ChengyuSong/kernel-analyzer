# CFL-Reachability Architecture, Optimizations, and VSnapshot

This document describes the current CFL-reachability-based call graph pipeline,
the performance/soundness-oriented optimizations in `CallGraphPass`, and the
serialized `V`-relation snapshot format (`VSnapshot`) for downstream reuse.

## 1. Architecture Overview

The indirect-call resolution pipeline is built around a CFL-reachability solver:

1. LLVM IR is traversed in `CallGraphPass` (`src/lib/CallGraph.cc`).
2. Constraints are emitted via `CFLEdgeBuilder` using a points-to grammar.
3. `gracfl::SolverFWGramParallel` computes closure over labeled relations.
4. The `V` relation (value aliasing) is queried to resolve indirect call targets.

At a high level:

- `AndersNodeFactory` creates node IDs for IR values/objects.
- `CFLEdgeBuilder` stores grammar-labeled input edges.
- The CFL solver computes transitive closure.
- `handleIndirectCall(...)` uses `V`-reachable function nodes plus type checks
  (and optional field evidence filtering) to add call graph edges.

## 2. Implemented Optimizations

### 2.1 Must-like local representative merge

Enabled by default with:

- `--cfl-local-rep-merge=true`

This merges clearly equivalent local pointer values during function parsing
(`runOnFunction`) for patterns like:

- copy-like bitcasts
- zero-offset GEP aliases
- `phi` where all incoming values are in the same class
- `select` where both branches are in the same class

This reduces local node/edge fanout before closure.

### 2.2 Canonical map-back for sound querying

A persistent canonical map is maintained across functions. This is critical:

- graph construction uses representative nodes
- querying (indirect calls, field-store map, custom allocators) must also query
  canonical representatives and class members

Without map-back, querying raw nodes can miss reachable functions and reduce
indirect-call match quality.

### 2.3 Non-escaping local alloca summary

Enabled by default with:

- `--cfl-local-alloca-summary=true`

For conservative non-escaping pointer allocas, explicit load/store chains are
summarized into store-set -> load-set edges. This cuts graph complexity while
remaining suitable for the current flow-/field-insensitive setting.

### 2.4 Canonical-class dedup in alias-set traversal

When scanning large `V` sets, the same canonical class can appear through many
member nodes. The implementation deduplicates by canonical root before class
expansion in hot paths:

- custom allocator discovery
- field-store map build
- indirect-call resolution

This lowers redundant work without changing semantics.

## 3. VSnapshot: serialized `V` relation

Because whole-program CFL solving is expensive and useful beyond call graph
construction, the final `V` relation can be exported and reused.

### 3.1 Export

Use:

```bash
release/lib/KAMain <bitcode...> --v-snapshot /path/to/out.vsnap
```

The snapshot is written by standalone code in:

- `src/lib/VSnapshot.h`
- `src/lib/VSnapshot.cc`

The call graph pass entry point is:

- `CallGraphPass::dumpVSnapshot(...)`

### 3.2 What is stored

The snapshot stores representative-space aliasing data in compact form:

- `node_to_rep`: original node -> representative ID
- `rep_to_node`: representative ID -> canonical original node
- `rep` rows: sorted destinations for `V` aliasing (delta-varint encoded)
- metadata JSON (analysis config/version)
- optional named node index for query ergonomics

Rows are serialized in a streaming manner to avoid materializing all rows at
once in memory during export.

### 3.3 Python loader and query API

Standalone Python module:

- `tools/vsnapshot.py`

Basic usage:

```python
from tools.vsnapshot import VSnapshot

s = VSnapshot.load("/path/to/out.vsnap")

# node-level queries
rep = s.rep(1234)
aliases = s.aliases_of_node(1234)
may = s.may_alias(1234, 5678)

# name-assisted queries (if name index exists)
nodes = s.resolve_name("foo")
```

## 4. Notes for downstream LLM/data-dependency analysis

- The snapshot is a reusable alias substrate for later analyses.
- For robust pipelines, treat `(snapshot metadata + IR/build hash + flags)` as
  a compatibility key.
- If your downstream analysis is function-centric, consider building secondary
  cached projections (for example, function summaries) from the snapshot rather
  than re-solving CFL each time.
