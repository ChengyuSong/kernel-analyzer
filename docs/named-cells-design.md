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

- Every cell (Deref target) has an **unnamed shadow**. A single-leaf named store (or initializer
  slot) of name n also writes the cell's shadow for n. Every other write into a cell also writes
  its unnamed shadow: unnamed stores, int-provenance stores, memcpy, CPY/MOVE/ST summary atoms,
  asm closures, fieldwise and residue copies, and writes wired by later resolution iterations.
  This is checked in one place, `addAssignmentEdge` → `fileUnnamedWrite`, so no site has to be
  enumerated.
- A **named load** reads its name's shadow and the unnamed shadow. An unnamed load reads the cell
  itself, which still receives every write, exactly as without names.
- A shadow has no Deref edge of its own. The solver keeps it as a **satellite** of its cell's
  class: every class merge (cluster join, a-SCC collapse) merges the two classes' shadows of each
  name. So a merged class keeps its content by name, the Lean `NDeriv` planes, and the cluster
  registry is unchanged (no name in the key). The relevance oracle `--cfl-bidi-prune` counts a
  shadow as part of its cell's partition.
- Shadows are presolve barriers and are never collapsed with values (a-SCC). They never mint an
  identity. A root minted on a class (content nobody in the program wrote) is seeded into the
  unnamed shadows of the class's raw cells.
- **Copies keep names.** A cell-to-cell copy relays unnamed to unnamed, and each name's shadow to
  the same name's shadow. A byte copy keeps offsets, so content keeps the name it was stored
  under. Because memcpy inside wrappers is untyped, the relayed names are read off the solution:
  after each fixpoint, every name with a cluster at one of the source pointer's facts is wired.
  The new edges enter the next outer iteration, like newly resolved callees.

Unsupported combinations are refused (CLI): channel cells, lazy addresses, batched roots, lazy
minting, slicing.

## 3. Why no certificate census

Plan 3.4 certified a name when no store can reach its cells without naming it, using a syntactic
hazard list. With `--cfl-named-planes`, every write that carries no name lands in the unnamed
shadow of the cells it *actually* reaches, according to the solve. So bulk copies, escapes,
atomics, untyped stores and summaries need no hazard counter: their effect is per object, not
per name program-wide. A named load always reads the unnamed plane. The one remaining
hypothesis is `PunFree`: a named store and a named load of one concrete cell use the same name.
That is type data in the answer path, the same assumption the field tables make; section 1 lists
what is detected.

## 4. Proof

- `realize_sound`: against the exact semantics with identities, every concrete flow is a flow of
  the realized graph (satellite merges `mal_sat` plus identity seeding), given the graph
  construction (`Realizes`) and `PunFree`.
- `realize_removal_only`: projecting shadows onto their cells maps every solver derivation onto
  today's grammar. Named planes only remove answers.

## 5. Measurements (2026-10-02)

Gates (satellite binary, `test/consumer-gate.sh` over libpng, the SoK small set, nm-new, libjpeg,
sqlite3 and httpd; 44 runs per side):

- G1, flag off against HEAD 2e2e0cd (`test/consumer-diff.sh`): `SAME` on all 44 runs.
- G2, flag on against flag off (`test/subset-gate.py` with the SoK fuzz ground truth; httpd by its
  ICALL lists): no pair added anywhere, and no fuzz-observed pair removed.

Pairs removed by named planes:

| run | off | removed |
|---|---|---|
| nm-new O0 base (json pairs) | 74,829 | 21: `nm.c` `format->print_*`, 6–9 → the 3 of that field |
| nm-new O3 base (json pairs) | 73,412 | 21 (same sites) |
| httpd base (ICALL pairs) | 144,454 | 115: 111 at `apr_dbd_transaction_start`, 4 at `ap_set_config_vectors` |
| httpd full | 63,877 | 1 (`apr_dbd_transaction_start` → `ap_unixd_accept`) |
| the other 40 runs | | 0 |

What the unnamed plane costs in precision. At every icall whose callee is loaded through a name
(verbose 2), these are the targets in the name's plane versus those that arrive only through the
unnamed plane:

| run | sites | in the name's plane | unnamed plane only |
|---|---|---|---|
| tiffsplit O0 base | 125 | 18,121 | 5,264 |
| sqlite3 O0 base | 199 | 22,257 | 112,779 |
| nm-new O0 base | 1,525 | 20,812 | 795,884 |

So at those sites about 97% of the targets on nm-new and 84% on sqlite3 come only through
writes that carry no name. Assuming no unnamed write reaches a named field (the field tables'
counted blind spot) would remove them. Named planes do not assume it.

Why the unnamed plane is full, on tiffsplit:
- `tif_close.c:53` (`(*tif->tif_cleanup)(tif)`): the `tiff+cleanup` plane holds exactly the 9
  `*Cleanup` functions (fuzzing observed 7, all among them), but the answer is 58.
- Every libtiff allocation is one object (`_TIFFmalloc::call`). Its unnamed plane receives
  `void *` out-parameter stores (`*va_arg(ap, void**) = ...` in `_TIFFVGetField`) of values read
  by unnamed loads of that same object, which in a field-insensitive cell is everything. Copies
  out of it carry every name into every name plane.
- Neither a FRESH summary for `_TIFFmalloc` nor 13 field buckets changed the site.

## 6. Cost

The first realization keyed clusters by (origin, shift, name), which multiplies the registry by the
names that reach each origin. The satellite realization keeps the registry near today's size. The
remaining cost is the shadow nodes themselves: every cell has an unnamed shadow, and named stores
and loads add one per (cell, name). sqlite3 goes from 23,860 to 639,728 dense classes, and the solve
is 13x slower:

| run | clusters: off / keyed / satellites | time: off / keyed / satellites |
|---|---|---|
| tiffsplit FI | 1,081 / 171,442 / 1,311 | solve 65 / 409 / 155 ms |
| tiffsplit, 13 buckets | — | run 5 / 58 / 7.1 s |
| sqlite3 FI | 6,001 / 5,223,681 / 8,296 | solve per iteration 0.9 s / 270 s / 11.9 s |

## 7. Open decision

Precision: stay sound and make heap/offset precision for untyped writers the prerequisite (the
field tables stay until named planes match them); or an explicit, counted mode that skips the
unnamed plane (the tables' assumption); or shelve the flag.
