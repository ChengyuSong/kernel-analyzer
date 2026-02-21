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

Perform CFL solving at the library level (group of TUs), then use the solved
V-reachability to compress the constraint graph via V-SCC (value-flow strongly
connected component) merging. These compressed constraint graphs are serialized
to `.cflcg` files and composed at link time for whole-program analysis.

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

Level 2: Library-level compression (--cfl-compressed-output)
  1. Build constraint graph from all TUs in the library group
  2. Solve CFL on the combined per-library graph  (SolverFWGramParallel)
  3. Compute V-SCCs from solved V-reachability    (computeVSCC)
  4. Compress: remap edges through V-SCC, deduplicate, build symbol
     table and funcNodes metadata                 (compressConstraintGraph)
  5. Serialize to .cflcg file with metadata JSON  (exportCompressedGraph)

Level 3: Whole-program composition (--cfl-compositional --cfl-compressed-input)
  1. Load compressed graphs from library .cflcg files
  2. Assign each graph a node offset in unified space
  3. Build boundary symbol occurrence map
  4. Union-find merge matching boundary nodes across graphs
  5. Dense remapping through union-find representatives
  6. Remap and deduplicate edges into combined graph
  7. Solve CFL on the combined compressed graph
  8. Build reverse map: dense node -> function names (denseToFuncNames)
  9. Deserialize per-TU funcFieldStores from metadata + augment with
     cross-TU V-reachability at stor: boundary symbols
  10. Resolve indirect calls using composed V-reachability with
      type-compatibility and field-store filtering
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
| `stor:`    | `stor:<structName>#<fieldIdx>#<counter>` | Field store value nodes |

GUIDs are numeric identifiers derived from symbol names. The `icall:` prefix
uses deterministic IDs attached as `ka.icall.id` LLVM metadata during
constraint graph construction. The `stor:` prefix encodes field store locations
for cross-TU field store map reconstruction.

Internal nodes (static functions, local variables, temporaries) do not need
symbols -- they participate only through their edges in the compressed graph.

## Indirect call resolution

After composition and CFL re-solve, indirect calls are resolved by:

1. Looking up the `icall:<id>` symbol to find the fptr's dense node ID
2. Querying the V-set at that node in the composed reachability graph
3. Mapping V-reachable nodes to function names via `denseToFuncNames`
4. Filtering candidates by type-compatibility (`isCompatible`)
5. Filtering by struct-field-aware field store map (`composedFieldStores`)

### Cross-TU field store map

The field store map tracks which (struct, field) pairs each function's address
is stored to. It enables rejecting indirect call targets at call sites where
the function pointer is loaded from a struct field the target was never stored
to.

Two sources populate `composedFieldStores`:

1. **Per-TU metadata** (from `.cflcg` `fieldStores` JSON): captures functions
   that syntactically perform stores to struct fields within their TU. This
   covers 44 functions in the libpng test case and provides precise field info.

2. **Cross-TU V-reachability** at `stor:` boundary symbols: when a function's
   address crosses a TU boundary before being stored to a struct field (e.g.,
   fuzzer passes `&default_free` to `png_set_mem_fn` which stores it to
   `png_struct_def` field 4), neither TU's per-TU analysis can connect the
   function to the field store. The `stor:` symbols export field store value
   nodes as boundary symbols; after composition, V-reachability at those nodes
   discovers the cross-TU function-to-field-store flows.

   **Guard**: V-reachability entries are only added for functions with **no**
   existing per-TU entry. The composed V-relation is less precise than per-TU
   analysis, so adding its results to functions that already have precise
   entries would introduce false field matches and weaken the filter.

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

  std::string metadataJson;              // JSON with fieldStores, etc.
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
# Level 2: Generate compressed graphs per library
kanalyzer lib1_tu1.o lib1_tu2.o --cfl-compressed-output lib1.cflcg
kanalyzer lib2_tu1.o            --cfl-compressed-output lib2.cflcg
kanalyzer app.o                 --cfl-compressed-output app.cflcg

# Level 3: Whole-program composition
kanalyzer lib1_tu1.o lib1_tu2.o lib2_tu1.o app.o \
  --cfl-compositional \
  --cfl-compressed-input lib1.cflcg \
  --cfl-compressed-input lib2.cflcg \
  --cfl-compressed-input app.cflcg \
  --callgraph-json output.json
```

Note: Level 3 loads all TU bitcode files (for module initialization, type info,
and indirect call site metadata) but skips the expensive full CFL solve,
using the composed compressed graph results instead.

## Cost analysis

For a project with k translation units each of average size n/k:

- **Monolithic**: O((n)^3) solve time
- **Compositional**: k * O((n/k)^3) per-TU + O((n_compressed)^3) composition
  = O(n^3 / k^2) + O((n_compressed)^3)

With compression ratios of 30-70%, the composition-level graph is substantially
smaller than the monolithic graph. The per-TU solves are embarrassingly parallel.

Additional savings from caching: when a TU/library does not change, its
compressed graph is reused without re-solving.

**Known issue**: Level 2 library analysis on separate TUs can be slower than
monolithic analysis on LTO-merged IR because separate compilation produces more
nodes (on-demand nodes for cross-TU function references) and the CFL fixed-point
reaches more edges through the additional connectivity. In the libpng test case,
Level 2 (512s) is ~4x slower than monolithic (135s) due to 18K vs 12.7K nodes
and edge explosion in the second iteration (140M vs 92M final edges).

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
- **15 extra edges** (imprecision from field-insensitive cross-library flows)
- Composition solve: ~100ms on 3137 dense nodes, 3274 edges
