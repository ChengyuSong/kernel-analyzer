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

### Why V-SCC merging is sound and precise

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

V includes epsilon (identity) and is transitively closed, which is what makes
V-SCC merging a valid congruence.

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
  4. Compute V-SCCs from solved V-reachability    (computeVSCC)
  5. Compress: remap edges through V-SCC, deduplicate, build symbol
     table and funcNodes metadata                 (compressConstraintGraph)
  6. Store compressed graph in memory              (perTUGraphs)
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

  std::string metadataJson;              // reserved for future metadata
};
```

Serialized to `.cflcg` files via `saveCompressedGraph()`/`loadCompressedGraph()`
in `CompressedGraph.{h,cc}`. The format is a binary header followed by
length-prefixed sections for edges, symbols, funcNodes, and metadata.

## CLI options

```
--cfl-compressed-output <path>    Export compressed graph to .cflcg file
--cfl-compressed-input <path>     Load compressed graph (repeatable)
--cfl-compositional               Run compositional solve from inputs
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
