# Named cells: design, realization, and first measurements

Plan: `docs/plan-named-cells.md` Part B. Model: `proof/lean/CompositionalCFL/NamedCells.lean`
(obligations in `proof/lean/GAPS.md`, "Named cells"). Flag: `--cfl-named-planes` (default off).
Status 2026-10-02: work in progress. The mechanism is sound and removal-only, but it removes
almost nothing on the measured programs (section 5), and it is expensive (section 6).

## 1. What a name is

The name of a scalar access is the innermost named struct type that contains the accessed leaf
field, with the leaf's byte offset in that struct (`ka::AccessNames`, `src/lib/NamedCells.{h,cc}`):

- Array elements fold onto element 0, so every element of an array field shares one name.
  A variable index into an array keeps the name.
- Literal structs are transparent.
- One descent (`ofSlot`) serves both sides. Loads and stores reach it through their GEP chain
  (`ofAccess`), initializer slots through the global's type. So a store and a load of the same
  field get the same name.
- Unnamed accesses: no struct type on the address, an offset leaving the struct (`container_of`,
  tail arrays), an access crossing a leaf or landing in padding, a union on the path, or a
  *pun*. A pun is a chain that casts a position to a struct the enclosing layout does not have
  there, or a base pointer indexed as two struct types neither of which sits at offset 0 of the
  other (`scanBases`).

Because names are canonical leaves, layout aliasing is equality: a field of an embedded struct
has exactly one name, the embedded struct's.

## 2. Realization: shadow cells

The solver keeps no name-indexed planes inside a class. Instead:

- Every cell (Deref target) has an **unnamed shadow**, and named accesses add a shadow per
  (cell, name). A single-leaf named store or initializer slot of name n also writes the cell's
  shadow for n. Every other write into a cell is classified in one place
  (`addAssignmentEdge` → `fileUnnamedWrite`), so no write site has to be enumerated:
  - a **copy** from another cell (memcpy, CPY summaries, field-wise and residue copies) relays
    each name's shadow to the same name's shadow and unnamed to unnamed. A byte copy keeps
    offsets, so content keeps the name it was stored under. The names to relay are read off the
    solution after each fixpoint (memcpy in wrappers is untyped), and the new edges enter the
    next outer iteration like newly resolved callees;
  - a **typed write**: its pointer has a struct position (the GEP chain, a global's or stack
    slot's declared type, or, for summary atoms, the summarized function's formal). If the write
    covers one leaf, it is filed under that leaf's name. Otherwise (variable offset, several
    leaves, unknown extent, union, pun) it goes to the unnamed shadow and **opens** every leaf of
    the structs it may lie in. Writes declare their shape (`CellWriteSize`: size, an offset the
    cell does not carry, value move vs. copy);
  - an **untyped write** (no struct position: `void *` out-parameters, a loaded pointer of unknown
    type, a literal-typed initializer slot whose global is read as no single struct) goes to the
    unnamed shadow. It is the **counted blind spot** (section 3).
- A **named load** reads its name's shadow, plus the unnamed shadow unless its name is certified
  (never opened). Opening a name later adds the read (monotone, before the next solve). An
  unnamed load reads the cell itself, which still receives every write, exactly as without names.
- A shadow has no Deref edge of its own. The solver keeps it as a **satellite** of its cell's
  class: every class merge (cluster join, a-SCC collapse) merges the two classes' shadows of each
  name. So a merged class keeps its content by name, the Lean `NDeriv` planes, and the cluster
  registry is unchanged (no name in the key). The relevance oracle `--cfl-bidi-prune` counts a
  shadow as part of its cell's partition.
- Shadows are presolve barriers and are never collapsed with values (a-SCC). They never mint an
  identity. A root minted on a class (content nobody in the program wrote, i.e. from outside) is
  seeded into every shadow of the class's raw cells, so a certified load still sees it.
- Literal-typed globals (designated initializers, unions, bitfields) have their slots named by
  the struct the program reads them as: the one struct their GEPs index them as, else their
  debug-info type.

Unsupported combinations are refused (CLI): channel cells, lazy addresses, batched roots, lazy
minting, slicing.

## 3. The certificate and the blind spot

The precision comes from the certificate (plan 3.7): without it every named load reads the
unnamed plane, and where the solve has collapsed objects that plane holds everything (the first
gate round, section 5). The certificate asks a type question instead of a reach question: can
any writer that names no single leaf target struct S? Typed writers answer it by construction
(they open what they may cover). Untyped writers cannot answer it.
`--cfl-named-untyped` decides what they do (plan decision 7):

- `count` (default with the flag): they open nothing. This is the one assumption, the same blind
  spot the field tables make, and it is counted per run: `NamedCells: ... blind spot: N untyped
  writes into cells`, with the writing functions.
- `open`: they open every name, so no load skips the unnamed plane (sound, and the first gate
  round's behavior).

The other hypothesis is `PunFree`: a named store and a named load of one concrete cell use the
same name. That is type data in the answer path; section 1 lists what is detected.

## 4. Proof

- `realize_sound`: against the exact semantics with identities (content from outside is readable
  under every name), every concrete flow is a flow of the realized graph (satellite merges
  `mal_sat` plus identity seeding), given the graph construction (`Realizes`, where only
  uncertified named loads read the unnamed shadow), `PunFree`, and `CertNamed` (unnamed content
  never reaches a certified load: discharged for typed writers, assumed for untyped ones).
- `realize_removal_only`: projecting shadows onto their cells maps every solver derivation onto
  today's grammar. Named planes only remove answers.

## 5. Measurements

### 5.1 With the certificate (2026-10-03, `--cfl-named-untyped=count`)

Base configuration (summaries, no field tables). "named" is base plus `--cfl-named-planes`;
"tables" is the shipped "full" configuration (field tables plus proposed summaries). Recall is
checked against the SoK fuzz ground truth (observed pairs found / observed pairs at sites we
answer). G3 counts the sites where the tables narrow the base answer and named planes are at
least as tight:

| program | base | named | tables | recall (all three) | G3 |
|---|---|---|---|---|---|
| sqlite3 fuzzershell O0 | 19,106 | **2,037** | 10,288 | 329/329 | 119/119 |
| nm-new O0 | 74,829 | **3,437** | 63,340 | 223/223 | 692/692 |
| tiffsplit O0 | 2,391 | **679** | 1,872 | 90/90 | 27/27 |
| flvmeta O0 | 102 | 78 | 86 | 10/10 | 4/4 |
| djpeg O0 | 163 | 132 | 156 | 5/10 | 1/1 |
| cflow O0 | 90 | 80 | 100 | 23/24 | (none) |

Named planes add no pair anywhere. Examples:
- tiffsplit `tif_close.c:53` (`(*tif->tif_cleanup)(tif)`): 58 → the 9 `*Cleanup` functions
  (fuzzing observed 7, all among them); `tif_dir.c:673` (`vsetfield`): the 9 `*VSetField`.
- libpng: every callback site names exactly what the harness installs (`user_read_data`,
  `default_free`, `limited_malloc`, `longjmp`, the 5 row filters); sites loading callbacks it never
  sets are empty.

Blind spot, counted per run: sqlite3 3,125 untyped writes into cells (26 of 1,150 names opened by
typed writers, 8,895 loads skip the unnamed plane); nm-new 3,637 (162 of 1,123 names opened,
6,888 loads skip it). The run log lists the writing functions (verbose 2) and, at verbose 3, the
first writer that opened each name.

Getting here took six corrections, each found by a real flow:
1. Copies keep names (a memcpy of a heap object carried every name into the unnamed plane).
2. Summary atoms declare their write shape. Field-insensitive summary cells drop the byte
   offset, so an ST atom writing `read_data_fn` was filed under field 0.
3. Summary atoms are positioned by the summarized function's formal: the call site's actual is
   an untyped loaded pointer, so `png_set_read_fn`'s write fell into the blind spot.
4. Identities get their own plane: seeding them only into a cell's existing shadows missed
   certified loads of names the minting cell never had.
5. The presolve cone crosses names. Icall operands read only through shadows (barriers) had
   left the cone empty (5 of 9,116 nodes on tiffsplit), so values stored under a name read at an
   icall were V-merged into the soup (`vsetfield` carried every `vgetfield`).
6. A write into a union field opens only the structs inside the union. Opening the enclosing
   `Walker` opened `xExprCallback` (sqlite3).

The first full gate round with the certificate passed at -O0 but **lost fuzz-observed pairs at
-O3** (tiffsplit 29, sqlite3 11, djpeg 3). At -O3 the blind spot is false as stated: the
optimizer erases the struct types that named the writes. Each loss came from a write that the IR
still types, just not through a GEP:

7. Struct-path TBAA: instcombine turns field GEPs on fresh objects into byte GEPs
   (`gep i8, %tif, 928`), but the access keeps its `!tbaa` tag (base struct `tiff`, offset
   928). Loads and stores without a struct GEP are named from it.
8. Base pointers typed by debug info: a formal by its subprogram's parameter type, any other
   value by the variable a `dbg.value` describes it (or a no-op cast of it) as; anonymous
   structs by their typedef. This covers SLP-vectorized pair copies whose TBAA is merged to "any
   pointer".
9. Pointer-vector accesses name each lane: a `store <2 x ptr>` files the whole value under each
   lane's name (a superset); a vector load reads every lane's planes.
10. Structs only debug info still describes (`%struct.ppm_dest_struct` vanished from djpeg's IR
    at -O3) are descended through their debug-info members, handing over to IR types where the
    module still has them; their own leaves get the names their IR type would have had.

Final gate round (binary with all ten corrections; 44 runs per side: libpng ×4, the SoK small
set and nm-new at O0/O3 full/base, libjpeg, sqlite3, the exact-presolve runs, httpd):
- G1, flag off against 2e2e0cd: SAME on all 44 runs.
- G2, flag on against flag off: no pair added in any run, and no fuzz-observed pair removed.
  Selected totals, flag off → on (gate's ICALL lists): nm-new O3 base 114,001 → 9,111,
  sqlite3 O3 base 21,120 → 2,389, httpd base 144,454 → 23,135, httpd full 63,877 → 23,224.
- Run time falls where answers shrink: nm-new O0 base 627 s → 42 s (fewer callee edges are
  wired in later iterations).

With these, the -O3 losses are gone (tiffsplit, sqlite3, djpeg O3: no fuzz-observed pair
removed). All naming sources (GEP chains, declared types of globals and stack slots, TBAA,
debug-info types) are the same kind of evidence: what the program declares the memory to be.
`PunFree` is the assumption that this declaration holds at run time.

### 5.2 Without the certificate (first realization, 2026-10-02)

Every named load read the unnamed plane. Gates: flag off identical to 2e2e0cd on 44 runs, flag on
removal-only, no fuzz-observed pair lost. Removals only on nm-new base (−21 at O0 and O3, the
`nm.c` `output_fns` dispatch) and httpd (base −115, full −1). At named callee loads the unnamed
plane carried 84% (sqlite3) and 97% (nm-new) of the targets. Cause: objects the solve has
collapsed (all libtiff allocations are one `_TIFFmalloc` object) receive every untyped write.
This is why the certificate is load-bearing (plan 3.7).

## 6. Cost

Solve time per iteration and dense classes, sqlite3 fuzzershell O0 base:

| realization | classes | solve per iteration |
|---|---|---|
| off | 23,860 | 0.9 s |
| keyed clusters (first attempt) | — | 270 s (5.2 M cell clusters) |
| satellites, eager shadows | 639,728 | 11.9 s |
| + copies inside one class not relayed | ~40,000 | 4.2–4.6 s |
| final (cone and union corrections) | — | 3.9 s |

All 334 sqlite3 copies are inside one class at the fixpoint, where relaying a plane onto itself
is a no-op. The remaining 5× is the eager shadows: every cell has an unnamed and an identity
shadow, and every named access a name shadow. Plan 3.7 item 1 (planes created lazily, when a
class sees a second name) is the next step.

## 7. Open items

1. Laziness (plan 3.7.1).
2. Decision 7 (plan section 6): `count` (the blind spot, counted) or `open` as the default for
   untyped writes.
3. Remove the field tables (`--cfl-regfield-apply`, `--cfl-regfield-obj`; rule 1) once named
   planes are the default: G3 holds per site on the six programs measured.
