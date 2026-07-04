# Compositional CFL-Reachability Analysis

## Motivation

The current whole-program CFL-reachability analysis builds a single constraint
graph from all translation units and solves it monolithically. This has two
scalability problems:

1. **Graph size**: for large projects (e.g., binutils), the constraint graph can
   have millions of nodes and edges. CFL solving is superlinear (~O(n^3) worst
   case), so large graphs are disproportionately expensive.

2. **Redundant work**: projects with shared libraries (e.g., libiberty, libbfd)
   require rebuilding and re-solving the entire graph for each utility
   (objdump, readelf, nm, ...), even though the library analysis is identical.

## Approach

Perform CFL solving per translation unit, then use the solved V-reachability
to compress each TU's constraint graph via V-SCC (value-flow strongly connected
component) merging. These compressed constraint graphs are composed for
whole-program analysis, either in-memory or serialized to `.cflcg` files for
caching across builds.

### Why V-SCC merging is sound (with a precision caveat)

After per-TU CFL solving, nodes in the same V-SCC have mutual V-reachability,
meaning they have identical points-to sets. Two properties guarantee that
merging V-SCC nodes in the constraint graph preserves the whole-program result:

1. **Monotonicity**: CFL-reachability is monotone -- adding edges (from cross-TU
   connections) can only create more reachability, never less. Per-TU V-paths
   are a subset of whole-program V-paths, so per-TU V-equivalences hold in
   the whole-program solution.

2. **Congruence**: merging two V-equivalent nodes is equivalent to adding mutual
   `a`-edges between them, which is strictly weaker than the V-equivalence that
   already exists. Any CFL derivation in the merged graph can be expanded to a
   valid derivation in the original graph by inserting the existing V-path at
   the merge point.

This is strictly more powerful than pre-solve OVS, which can only merge nodes
in copy-edge SCCs (direct `a`-edge cycles). Post-solve V-SCC merging also
collapses nodes connected through dereference chains
(`(M? -a)* M? (a M?)*` paths).

### Grammar reference

The default P2 grammar (from `Global.h`):

```
M  = -d V d                           (memory alias)
V  = (M? -a)* M? (a M?)*              (value flow)
```

V includes epsilon (identity) and is symmetric, but it is **not** transitively
closed: the pattern places all `-a` steps before all `a` steps, so `a`
followed by `-a` (common-sink) is excluded. Since `computeVSCC` merges nodes
that are mutually reachable through *chains* of V edges, an SCC can contain
pairs that are not pairwise V-related monolithically. Merging them is still
sound (it only adds derivations), but it can manufacture common-sink V facts
that monolithic V excludes — a source of extra (not missing) edges. See
[cfl-graph-explosion-and-scaling.md](cfl-graph-explosion-and-scaling.md) §2.3
for details; the accurate claim for this section is "sound, with bounded
extra smearing", not full precision preservation.

## Soundness proof (core compositional CFL)

This section states and proves soundness of the **core compositional CFL
solver** (graph construction + per-TU compression + boundary composition +
final CFL solve), with respect to the monolithic CFL analysis.

### Statement

Let:

- `G` be the monolithic whole-program constraint graph that would be built by
  the non-compositional pipeline.
- `Reach_G(X)` be CFL reachability in `G` under nonterminal `X` (`X in {V, M}`).
- `C` be the composed graph produced by Levels 1-3 in compositional mode.
- `Reach_C(X)` be CFL reachability in `C`.

**Theorem (sound over-approximation).**  
For every nonterminal `X` and every pair of program nodes `(u, v)` represented
in the composed graph:

`u Reach_G(X) v  =>  q(u) Reach_C(X) q(v)`

where `q` maps original nodes to their composed representatives.

So compositional analysis does not lose any monolithic CFL facts; it may only
add extra facts.

### Assumptions (implementation-matched)

1. **Boundary completeness.** Every cross-TU interaction that can participate in
   CFL derivations crosses one of the exported boundary categories:
   `func/arg/ret/vararg/glob/icall`.
   Additional precision symbols (`icallret`, `lret`, `gptr`, `gderef`) may be
   exported and improve convergence/precision but are not required by the
   minimal soundness argument above.
2. **Symbol consistency.** If two TU-local nodes denote the same program-level
   boundary entity, they receive the same boundary symbol.
3. **Per-TU edge preservation.** Per-TU compressed graphs preserve all TU-local
   edges modulo V-SCC quotienting.
4. **Same grammar.** Per-TU and composed solves use the same CFL grammar.

These are exactly what `compressConstraintGraph` and `runCompositionalSolve`
implement.

### Lemma 1: Per-TU quotient is edge-homomorphic

For each TU graph `G_i`, let `~_i` be V-SCC equivalence and `pi_i` its quotient
map. For every original edge `(a --L--> b)` in `G_i`, the compressed graph
contains `(pi_i(a) --L--> pi_i(b))`.

When `pi_i(a) == pi_i(b)` (intra-SCC edge), the edge becomes a self-loop on the
SCC representative. **These self-loops must be preserved**, not dropped. Although
the two endpoints are V-equivalent, the grammar requires traversal through
intermediate labeled steps (d, -d, a, -a) to derive V via the memory-alias
nonterminal M. Specifically:

- `M(x, scc) = -d(x, scc) · V(scc, scc) · d(scc, scc)` requires a `d` self-loop.
- `MA(x, scc) = M(x, scc) · -a(scc, scc)` requires an `-a` self-loop.

Without these self-loops, V-reachability through memory-alias chains across TU
boundaries is blocked in the composed graph. See "Bug fix: V-SCC self-loops"
below for details.

Therefore every derivation entirely inside one TU lifts through `pi_i`, provided
intra-SCC self-loops are retained.

### Lemma 2: Composition simulates cross-TU steps

In monolithic `G`, cross-TU flow uses boundary entities (formal/actual, returns,
globals, etc.). In `C`, nodes carrying the same boundary symbol are unioned by
union-find, so a monolithic boundary transition is simulated by equality of
representatives in `C`.

Hence any derivation segment that crosses TU boundaries in `G` has a
corresponding segment in `C`.

### Lemma 3: Derivation lifting

Take any monolithic CFL derivation `D` from `u` to `v`. Partition `D` into
maximal TU-local segments separated by boundary crossings.

- By Lemma 1, each TU-local segment maps to a valid segment in compressed TU
  space.
- By Lemma 2, each boundary crossing maps to a valid step in composed space.

Concatenating mapped segments yields a valid derivation in `C` from `q(u)` to
`q(v)` under the same nonterminal.

### Proof of theorem

Immediate from Lemma 3.

Thus composed reachability is a conservative superset of monolithic
reachability.

### Corollary for indirect-call target discovery

If indirect-call targets are extracted only from composed `V` reachability and
then filtered by predicates that are themselves conservative (never rejecting a
true target), target discovery remains sound relative to monolithic CFL.

In this implementation, `isCompatible` is conservative by design. The
IR-derived field-store filter is intended to be conservative (unknown => keep),
but a full formal proof for that filter requires additional assumptions about
completeness of the callback-tracing patterns.

### Current mechanization gaps (Lean model vs implementation)

Canonical tracker: `proof/lean/GAPS.md`  
See: [`../proof/lean/GAPS.md`](../proof/lean/GAPS.md)

The Lean model in `proof/lean` currently proves a reusable **soundness schema**
for compositional CFL, but not yet a full machine-checked proof of the exact
`CallGraph.cc` pipeline. Detailed gap list and status live in
`proof/lean/GAPS.md`.

In short, remaining work is to:

1. Discharge implementation-specific simulation obligations from code-level
   construction (`compressConstraintGraph` / `runCompositionalSolve`).
2. Align fixed-point modeling details (including current capped loops) with the
   formal iteration story.
3. Formalize and prove conservativeness of target filtering, allocator
   promotion, and solver-to-spec refinement.

## Bug fix: V-SCC self-loops and compositional edge construction

The initial implementation had three bugs that caused compositional mode to miss
all indirect call targets in certain cross-TU configurations (e.g., function
pointers passed through interface functions defined in a separate TU).

### Bug 1: Missing actual-to-formal edges for external calls

**Location**: `CallGraph.cc`, `handleCall`

In per-TU mode, when a function calls an external (declared-only) function like
`kobj_map`, the callee's `Function` body is empty. The original code returned
early when `CompressedGraphOutput` was empty (no serialized output path), which
is always the case in per-TU compositional mode. This prevented creation of
actual-to-formal assignment edges for cross-TU calls.

**Fix**: Skip the early return when `CFLCompositional` is enabled. Boundary
symbols (`arg:<GUID>:<N>`, `ret:<GUID>`) are emitted for the declared function's
parameters even without a body, so the composition step can later connect them
to the definition's formals in the other TU.

### Bug 2: V-SCC compression dropped intra-SCC self-loops

**Location**: `CallGraph.cc`, `compressConstraintGraph` step 1.5

V-SCC compression collapses all nodes in a V-SCC to a single representative.
When two nodes `a` and `b` are in the same V-SCC, any edge `a --L--> b` becomes
a self-loop `scc --L--> scc`. The original implementation dropped all self-loops
under the assumption that they are redundant — since V-equivalence already
holds, no additional derivations are possible.

**Why this is wrong**: V-equivalence holds *within the per-TU solved graph*, but
the composed graph introduces new cross-TU edges that can create derivation
paths *through* the SCC node. These paths need intermediate grammar steps:

```
M(x, scc) = -d(x, scc) · V(scc, scc) · d(scc, scc)
```

Here `x` is a node from another TU connected to `scc` via a `-d` edge after
boundary composition. To derive `M(x, scc)`, the solver needs `d(scc, scc)` —
a self-loop that was dropped. The V self-loop `V(scc, scc)` is free (V is
reflexive), but the terminal `d` self-loop is not.

Similarly, `MA(x, scc) = M(x, scc) · -a(scc, scc)` requires an `-a` self-loop.

**Concrete example**: In a two-TU test (`char_dev.ll` + `map.ll`):
- `map.ll` defines `kobj_map(probe, ...)` which stores `probe` to a struct
  field via a dereference chain
- `char_dev.ll` calls `kobj_map(exact_match, ...)` and later loads the fptr
  from the struct via `kobj_lookup`
- After per-TU V-SCC compression in `map.ll`, the pointer node and its
  dereference target (connected by `d/-d`) end up in the same V-SCC
- The `d(scc, scc)` self-loop is dropped
- During composition, `char_dev.ll`'s fptr node connects to `map.ll`'s SCC
  via boundary edges, but `M` derivation fails without the `d` self-loop
- Result: 0 targets resolved instead of 3

**Fix**: After V-SCC compression, explicitly add self-loop edges for all four
terminal labels (`a`, `-a`, `d`, `-d`) on every multi-node V-SCC. Single-node
SCCs don't need self-loops because they had no intra-SCC edges to begin with.

### Bug 3: Composition dropped self-loops from union-find merging

**Location**: `CallGraph.cc`, `runCompositionalSolve` step 6

During composition, edges are remapped through union-find representatives. When
two formerly-separate V-SCC nodes from different TUs are merged (because they
share a boundary symbol), an inter-SCC edge `a --L--> b` becomes a self-loop
`merged --L--> merged`. The original code skipped all self-loops with
`if (from == to) continue;`, dropping these edges.

**Why this is wrong**: These are not redundant self-loops — they encode real
relationships between formerly-separate nodes that were merged by boundary
composition. The composed CFL solver needs them to derive V-reachability through
the merged mega-node.

**Fix**: Remove the self-loop skip entirely. Self-loops from union-find merging
encode internal relationships in composed mega-nodes and must be kept.

### Summary

All three bugs stem from the same incorrect assumption: that self-loop edges on
SCC/merged nodes are always redundant. In a compositional setting, self-loops
preserve intra-SCC grammar derivability that cross-TU edges may later exploit.

## Pipeline

```
Level 1: Per-TU constraint graph construction
  1. Build constraint graph from LLVM IR          (CFLEdgeBuilder)
  2. On-demand nodes for declared (external) functions to capture
     cross-TU arg/ret data flow in compositional mode

Level 2: Per-TU compression (inside doModulePass, after Level 1)
  1. Build field store map from IR uses           (buildFieldStoreMapFromIR)
  2. Build local dense mapping for the TU's edges
  3. Solve CFL on the per-TU dense graph          (SolverFWGramParallel)
  4. Resolve indirect calls for this TU and append new call edges
     until TU-local fixed point                    (handleIndirectCall loop)
  5. Compute V-SCCs from solved V-reachability    (computeVSCC)
  6. Compress: remap edges through V-SCC, deduplicate, build symbol
     table and funcNodes metadata                 (compressConstraintGraph)
  6b. Add self-loop edges (a/-a/d/-d) for multi-node V-SCCs to preserve
      intra-SCC grammar derivability for composition
  6c. Export optional precision symbols:
      `icallret`, `lret`, `gptr`, `gderef`
  7. Store compressed graph in memory              (perTUGraphs)
  Optional: serialize to .cflcg file              (exportCompressedGraph)

Level 3: Whole-program composition (--cfl-compositional)
  1. Collect compressed graphs (in-memory perTUGraphs and/or .cflcg files)
  2. Assign each graph a node offset in unified space
  3. Build boundary symbol occurrence map
  4. Union-find merge matching boundary nodes across graphs
  5. Dense remapping through union-find representatives
  6. Remap and deduplicate edges into combined graph
  7. Solve CFL on the combined compressed graph
  8. Build reverse map: dense node -> function names (denseToFuncNames)
  9. Resolve indirect calls using composed V-reachability with
     type-compatibility and field-store filtering (funcFieldStores)
 10. Add composed summary edges `ret(target)->icallret(callsite)` and
     iterate composed solve until no new summary edges
 11. Run composed custom allocator confirmation using return-node aliasing
```

## Boundary nodes and symbol table

A boundary node is any node that may be referenced from another TU. The symbol
table maps boundary symbol strings to compressed (V-SCC) node IDs:

| Prefix     | Format                        | Source                |
|------------|-------------------------------|-----------------------|
| `func:`    | `func:<GUID>`                 | `Ctx->Funcs/ExtFuncs` |
| `arg:`     | `arg:<GUID>:<argIdx>`         | Function arguments    |
| `ret:`     | `ret:<GUID>`                  | Return nodes          |
| `vararg:`  | `vararg:<GUID>`               | Vararg nodes          |
| `glob:`    | `glob:<GUID>`                 | `Ctx->Gobjs/ExtGobjs` |
| `icall:`   | `icall:<icallID>`             | Indirect call fptrs   |
| `icallret:`| `icallret:<icallID>`          | Indirect call results |
| `lret:`    | `lret:<scopedFuncName>`       | Local-linkage returns |
| `gptr:`    | `gptr:globfield:<GUID>:<idx>` | Canonical global-field ptr nodes |
| `gderef:`  | `gderef:globfield:<GUID>:<idx>` | Canonical global-field deref nodes |

Purpose of extra precision symbols:

- `icallret:` anchors indirect-call result nodes so composed summary edges
  `ret(target) -> icallret(callsite)` can be added and iterated.
- `lret:` exposes return nodes for local-linkage targets that do not have a
  reusable external `ret:<GUID>` path in composed inputs.
- `gptr:` exposes canonical constant-GEP global-field pointer nodes for
  cross-TU union-find merging.
- `gderef:` exposes corresponding global-field dereference nodes so cross-TU
  memory-flow paths through shared globals remain connected after compression.

GUIDs are numeric identifiers derived from symbol names. The `icall:` prefix
uses deterministic IDs attached as `ka.icall.id` LLVM metadata during
constraint graph construction.

Internal nodes (static functions, local variables, temporaries) do not need
symbols -- they participate only through their edges in the compressed graph.

## Indirect call resolution

After composition and CFL re-solve, indirect calls are resolved by:

1. Looking up the `icall:<id>` symbol to find the fptr's dense node ID
2. Querying the V-set at that node in the composed reachability graph
3. Mapping V-reachable nodes to function names via `denseToFuncNames`
4. Filtering candidates by type-compatibility (`isCompatible`)
5. Filtering by struct-field-aware field store map (`funcFieldStores`)

Callsite field keys are extracted from the fptr load operand. For the common
pattern `load ptr, ptr gep(..., field)` where the GEP points to a nested struct
value (no explicit trailing `, 0`), the key is refined to nested field `0` so
callbacks in struct method tables (e.g., `sqlite3_mem_methods`) are
distinguished by slot.

### IR-based field store map

The field store map tracks which (struct, field) pairs each function's address
is stored to. It enables rejecting indirect call targets at call sites where
the function pointer is loaded from a struct field the target was never stored
to.

The map (`funcFieldStores`) is built directly from LLVM IR during
`buildFieldStoreMapFromIR`, using three strategies:

1. **Direct stores**: a `store` instruction writes a function pointer to a
   GEP-derived struct field (`store @func, gep(%struct, 0, fieldIdx)`).

2. **Global initializers**: a `ConstantStruct` or `ConstantArray` initializer
   contains a function pointer at a known struct field offset. Detected in
   `processInitializer` during constraint graph construction.

3. **One-level callback tracing**: a function pointer is passed as an argument
   to a call, and the callee stores that argument (or a cast/load through an
   alloca spill) to a struct field. Only one level of interprocedural analysis
   is performed — the callee's body is inspected but no further calls are
   followed. This handles the common callback-registration pattern (e.g.,
   `png_set_mem_fn(&png, &default_free)` where `png_set_mem_fn` stores the
   argument to `png_struct_def` field 4).

   The alloca spill pattern (`param -> store to alloca -> load -> store to GEP`)
   is traced to handle unoptimized (`-O0`) IR where parameters are spilled to
   stack slots before use.

`funcFieldStores` accumulates across all modules during `doModulePass`. Since
Level 3 composition loads all TU bitcode files, cross-TU callback tracing
works naturally — `getFuncDef` resolves declarations to definitions across TU
boundaries. No metadata serialization or CFL V-reachability is needed.

The field filter is alias-expanded using aggregate-copy aliases discovered from
`memcpy/memmove` on struct fields (`fieldAliasMap`), which prevents false
rejections when method tables are copied through parent structs.

## Bug fix: compositional sqlite allocator promotion

The sqlite reduced repro (`main.bc + malloc.bc + mem1.bc`) exposed several
composition-specific gaps that blocked confirmation of `sqlite3Malloc`.

### 1) Missing cross-TU connectivity for canonical global-field nodes

Canonical constant-GEP nodes (e.g., `@sqlite3Config` field pointers) can exist
in multiple TUs, but without boundary symbols they stay disconnected after
per-TU compression. Added boundary symbols for:

- `gptr:globfield:<GUID>:<field>`
- `gderef:globfield:<GUID>:<field>`

This allows union-find composition to merge shared global-field flow roots.

### 2) Per-TU edge slices dropped ptr<->deref edges for reused canonical nodes

When a canonical deref node already existed from an earlier TU, later TUs could
reuse it without re-emitting ptr<->deref constraints in that TU's edge range.
Added per-module deref-edge re-emission (once per canonical ptr per module),
so each TU compressed graph keeps local memory edge context.

### 3) Composed summary-edge growth for indirect-call returns

Composed solve now iterates:

- resolve icall targets from composed V,
- add `ret(target) -> icallret(callsite)` (+ inverse assign) edges,
- re-solve CFL,
- repeat until no new summary edges.

This lets return flow discovered through indirect targets feed later facts.

### 4) Local-linkage return symbols for composed summaries

Static/internal indirect targets may not have reusable external `ret:<GUID>`
symbols in cache combinations. Added `lret:<scopedFuncName>` for local
address-taken functions and fallback lookup in composed summary building and
composed allocator confirmation.

### 5) Allocsite short-circuit previously hid known allocator return flow

Treating known allocator calls as explicit allocsites is useful, but it
removed/avoided call-return propagation needed by composed allocator promotion.
Allocator call handling now also preserves `ret(callee) -> call-result` edges,
so known allocator return nodes remain visible in composed alias checks.

### 6) GUID-based ret lookup robustness

Composed return symbol lookup now uses `F->getGUID()` directly (plus `lret`
fallback), avoiding brittle `Function*` identity assumptions across
declaration/definition objects.

### Outcome

In compositional mode, seeded candidate `sqlite3Malloc` is now promoted:

- before: `{"candidates":["sqlite3Malloc"],"confirmed":["malloc"]}`
- after:  `{"candidates":[],"confirmed":["malloc","sqlite3Malloc"]}`

**Design rationale**: the previous CFL-based approach (`buildFieldStoreMap`)
queried V-reachability from store-site value nodes to discover which functions
flow to each field. Due to field insensitivity, V is symmetric through shared
struct dereference nodes, causing all functions stored anywhere in a struct to
appear V-reachable from all store sites in that struct. The IR-based per-fptr
approach avoids this imprecision by walking from each function pointer's uses.

## Serialization format

```cpp
struct CompressedGraphData {
  static constexpr uint32_t kVersion = 1;
  uint32_t numNodes;                     // dense V-SCC node count
  std::vector<gracfl::Edge> edges;       // compressed constraint edges

  // boundary symbol string -> compressed node ID
  std::unordered_map<BoundarySymbol, uint32_t, BoundarySymbolHash> symbolTable;

  // compressed node ID -> function names (address-taken functions only)
  std::unordered_map<uint32_t, std::vector<std::string>> funcNodes;

  std::string metadataJson;              // JSON metadata (analysis/cache key)
};
```

Serialized to `.cflcg` files via `saveCompressedGraph()`/`loadCompressedGraph()`
in `CompressedGraph.{h,cc}`. The format is a binary header followed by
length-prefixed sections for edges, symbols, funcNodes, and metadata.

Current `metadataJson` includes:

- `analysis_key`:
  - grammar labels (`a/-a/d/-d/M/V`)
  - grammar signature + fingerprint
  - analysis flags (`global_dedup`, `local_alloca_summary`)
  - `.cflcg` schema/tool version
- `covered_modules`: stable normalized module identifiers
- `module_hashes`: per-module SHA256 of input bitcode bytes

## CLI options

```
--cfl-compressed-output <path>    Export compressed graph to .cflcg file
--cfl-compressed-input <path>     Load compressed graph (repeatable)
--cfl-compositional               Run compositional solve from inputs
--cfl-cache-strict=<true|false>   Strict cache validation (default: true)
--cfl-cache-repair                Recompute invalid/missing modules from current IR
--cfl-cache-allow-duplicate-coverage
                                  Allow duplicate module coverage across inputs
```

Typical usage:

```bash
# All-in-one: per-TU solve + compose (no intermediate files)
kanalyzer tu1.o tu2.o tu3.o --cfl-compositional --callgraph-json output.json
```

```bash
# Two-phase with cached compressed graphs:

# Level 2: Generate compressed graphs per library
kanalyzer lib1_tu1.o lib1_tu2.o --cfl-compressed-output lib1.cflcg
kanalyzer lib2_tu1.o            --cfl-compressed-output lib2.cflcg
kanalyzer app.o                 --cfl-compressed-output app.cflcg

# Level 3: Whole-program composition from pre-built graphs
kanalyzer lib1_tu1.o lib1_tu2.o lib2_tu1.o app.o \
  --cfl-compositional \
  --cfl-compressed-input lib1.cflcg \
  --cfl-compressed-input lib2.cflcg \
  --cfl-compressed-input app.cflcg \
  --callgraph-json output.json
```

Note: Level 3 loads all TU bitcode files (for module initialization, type info,
indirect call site metadata, and IR-based field store map construction) but
skips the expensive full CFL solve, using the composed compressed graph
results instead.

### Cache validity policy (strict by default)

In compositional mode, cache inputs are validated against current bitcode
inputs before composition:

1. Coverage: union of all input `covered_modules` must exactly match the
   current module set.
2. Freshness: each covered module hash in `module_hashes` must match current
   SHA256.
3. Compatibility: `analysis_key` must match current grammar labels/signature
   and relevant flags (`global_dedup`, `local_alloca_summary`).
4. Duplicate ownership: a module may not be covered by multiple input caches
   unless `--cfl-cache-allow-duplicate-coverage` is set.
5. Boundary sanity: required boundary classes
   (`func/arg/ret/vararg/glob/icall`) must be present when expected from
   active IR/CFL boundary nodes.

Optional precision classes (`icallret`, `lret`, `gptr`, `gderef`) are not
strictly required by this check, but strongly improve composed precision and
allocator confirmation behavior.

On mismatch, diagnostics explicitly list:

- `missing`
- `stale`
- `duplicate`
- `incompatible`

and strict mode fails closed.

`--cfl-cache-repair` recomputes modules from current IR and resumes
composition. `--cfl-cache-strict=false` can be used for legacy/handcrafted
`.cflcg` inputs that do not carry full metadata.

## Cost analysis

For a project with k translation units each of average size n/k:

- **Monolithic**: O((n)^3) solve time
- **Compositional**: k * O((n/k)^3) per-TU + O((n_compressed)^3) composition
  = O(n^3 / k^2) + O((n_compressed)^3)

With compression ratios of 30-70%, the composition-level graph is substantially
smaller than the monolithic graph.

Per-TU solving avoids the edge explosion that occurred when all TUs were combined
into a single Level 2 graph. Each TU's graph is small (hundreds to low thousands
of nodes), so per-TU CFL solving is fast and the k per-TU solves are
embarrassingly parallel.

Additional savings from caching: when a TU/library does not change, its
compressed graph (`.cflcg` file) is reused without re-solving.

## Incremental rebuild

When a single source file changes:

1. Re-compile to LLVM IR (existing build system)
2. Re-run Level 2 on the affected library group only
3. Re-run Level 3 whole-program composition

Fits naturally into make/ninja dependency tracking:
`foo.c -> foo.o -> libfoo.cflcg -> whole-program`

## Validation

The test script `test/eval-compositional.sh` validates the compositional
approach against the monolithic baseline on the libpng read fuzzer:

1. Monolithic analysis on LTO-linked IR (ground truth)
2. Level 2 compressed graph generation for libpng16, magma, and fuzzer
3. Level 3 whole-program composition
4. `test/compare-callgraphs.py` compares indirect call edges

Current results (libpng test case):
- **SOUND**: 0 missing edges (compositional is a superset of monolithic)
- **14 extra edges** (imprecision from field-insensitive cross-library flows)
- Composition solve: ~100ms on ~3K dense nodes
