# Channel cells: pairwise-witnessed M instead of transitive clusters

Status: DESIGN + Lean model 2026-09-13 (approved direction); v1
implementation behind `--cfl-channel-cells`.

## Problem

The flows-to grammar's memory-alias relation is PAIRWISE-witnessed:

    M(c, d)  ⟺  ∃ (origin o, shift s): base(c) ⟶V (o,s)  ∧  base(d) ⟶V (o,s)

One store's content reaches one load through exactly one shared
witness key. The solver realizes M with union-find clusters
(`joinCluster`): every cell of a pointer class carrying fact (o,s)
is merged into the cluster keyed (o,s). Union-find classes are
TRANSITIVE: a cell whose owner carries {(o1,s1), (o2,s2)} anchors
both keys and forces cluster(o1,s1) = cluster(o2,s2). After that,
an o2-only writer's content reaches an o1-only reader with NO
common witness — a derivation that does not exist in the grammar.
The implementation over-approximates its own spec, exactly at
multi-key cells, and the coalescence is transitive across the
whole key graph.

Measured consequence (nm-new, 2026-09-13, docs in
memory/aict-weld-attribution): one cluster anchoring 400+
(origin, shift) keys across ALL 14 shift planes, glued by ~150
identity/synthetic origins (unwitnessed bfd fields); the vec/bed
initializer deposit cells sit inside, so every read in the cluster
sees all ~51 fns (SoK AICT 43.9 vs LLVM-CFI 8.1). Six other
mechanisms were eliminated by instrument before this one was
confirmed by the slice-key dump (b0b8395): fs residues, formal
confluence, arena allocators, O0 heap typing, wildcard/laundering
admissions (full ablation), presolve merges. The kernel weld
taxonomy (born-giant, tcp→ahci, EFI — docs/kernel-precision-
killers.md) is the same mechanism at scale: formal cells with
multi-origin facts ARE multi-key cells.

## Solution

Make the channel a first-class node — the id-keyed channel design
carried into the solver core. One node per realized key (o, s);
`joinCluster` stops merging and instead wires DIRECTIONAL copy
edges:

    store-cell --a--> channel(o,s)     for every key of the owner
    channel(o,s) --a--> load-cell      for every key of the owner

Content crosses store→load iff both witness one shared channel:
the grammar's M, by construction (Lean: `chanflow_iff_pairflow`).

Properties that fall out:
- Strictly tighter, sound by construction: PairFlow ⊆ ClusterFlow
  (Lean: `pair_le_cluster`), strict (`cluster_exceeds_pair` — the
  nm-new shape). Every answer change is removal-only ⇒ the gate is
  one-sided (new ⊆ old) + the filter-ledger × fuzz-GT join.
- fs becomes structural: channels are per-shift; cross-residue
  pooling is impossible rather than merely discouraged.
- The regfield/obj channels become certified REPLACEMENTS of
  specific channel nodes — one architecture, two tiers of
  evidence.

## v1 scope (flag-gated, old path untouched)

- Mono solve only: batch mode REFUSES the flag loudly (the batch
  event log records join events; the channel analog is edge
  additions — port after answers gate).
- `--cfl-verify-closure` REFUSES the flag loudly (C4-key mirrors
  the cluster predicate; verifier rule rewrite follows the answer
  gates — a verifier must mirror every solver rule change).
- Read-write cells (atomicrmw/cmpxchg): a both-directions cell
  would relay channel(k1) → cell → channel(k2), re-creating the
  transitive leak through itself. v1 keeps the OLD merge behavior
  for both-cells only, counted in a ledger (expected rare; split
  cells later if the count says otherwise).
- VX: channel(o,X) ↔ channel(o,s) bidirectional edges — same
  semantics and scope as today's bridges.
- Null hygiene: no channels for the NULL pseudo-object (same rule).

## v1 lessons (2026-09-14) → v2 wiring design

v1 reconstructed access direction from the dense graph (cell roles
from a/f/d edge shapes). Six wiring holes later, the uniform root
cause is clear: the encoding COLLAPSES access structure wherever
that is answer-exact under cluster semantics — result-as-cell
loads, store-cell ≡ stored-value (single-writer copy collapse, the
store a-edge becomes an intra-class self-loop and vanishes),
GEP ≡ base at FI, shared per-pointer deref nodes. Every collapse
erases exactly the direction/position information pairwise routing
needs; a class can simultaneously be the READER of one key and the
STORAGE of another (t_reg2: c8 = reader of (tab,0) and collapsed
content of (fd,+8)). Reconstruction downstream is unfixable by
construction, not by patching.

v2: record ACCESS MARKS in the instruction handlers, where the
direction is syntactic and collapse-immune:
  load  v = *p        -> mark (p, v, LOAD)
  store *p = v        -> mark (p, v, STORE)
  object/initializer  -> mark (addr, objNode, OBJECT)  (store-side)
  rmw/cmpxchg         -> both marks
The solver's channel flush iterates marks: for each fact (o,s) on
find(p): LOAD wires chan(o,s) -> find(v); STORE wires find(v) ->
chan(o,s). Marks reference node ids, so class merges never lose
them. cellsOf/joinCluster remain the cluster path; channel mode
replaces the join sweep's pend source with mark sweeps.

Fast gate for every iteration (user directive): the small
GT-bearing SoK programs (scratchpad fastgate.sh — tic, flvmeta,
cflow, lame, tiffsplit, cjpeg, djpeg, fuzzershell), cluster vs
channel: GT misses, mean fanout, one-sidedness; micro repros
t_reg.ll (const table) / t_reg2.ll (heap + bucket relay — THE
20-line reproducer of the sqlite3 fts3 loss) / t_litvt.ll.

## v2 as built (2026-09-15): unconditional split, no roles, no marks

The access-marks plan above turned out to be unnecessary. The
builder already states direction: a cell's build-time in-edges are
the values stored through its owner, its out-edges are the reads
(loads it feeds, GEPs on its content, its own downstream cells).
What v1 got wrong was inferring a ROLE per cell from the dense graph
after merges and then wiring one node in one direction (or merging
it). The flush now splits every cell unconditionally:

  write half = the cell itself: keeps its in-edges, gets an edge
               cell -> chan(o,s) for every key (o,s) of the owner;
  read half  = a fresh node taking over the cell's outA/outF/cellsOf,
               fed by chan(o,s) -> read-half for the same keys;
               not created for cells with no out-edges (object
               storage, dead assistants).

Two nodes cannot relay between the owner's keys (the write half never
receives channel content, the read half never feeds one), so
`rw_conduit_leaks` does not arise; a same-pointer store/load pair
still flows through the channel of any shared key
(`split_self_flow`). A cell merged with values by the exact presolve
(mutual flow) splits the same way: the merged node's in-edges are
stores, its out-edges are the uses — the RMW "read then write back
to the same location" is modelled without moving content between the
owner's keys, which is more precise than Andersen's rule and still
sound (a write-back to the location just read is a no-op).

Channel mode forces the exact presolve quotient and disables the
V-component cone quotient: both are symmetric unifications of the
kind the pairwise model removes (direction rule, 2026-09-15).

First measurements: t_reg / t_reg2 identical to cluster mode (t_reg2
no longer loses a target); default path byte-identical (smoke 4/4).
nm-new fs13 and the fastgate suite: see the campaign memory.

## Gates

1. Micro suite (test/t_*.bc incl. t_litvt) + cfl-smoke.
2. nm-new: AICT expected to fall toward the demand-driven range;
   ledger×GT = 0 observed records lost.
3. sqlite3/djpeg/httpd/pg/km: new ⊆ old everywhere; GT recall
   unchanged; SoK recall table stays 100%.
4. Perf at km then kernel: welded fact mass should SHRINK
   (pooled facts stop replicating); watch channel fan-in hubs.
5. Then: verifier rules, batch support, default-on decision
   (fix-or-remove the cluster path), full re-pin.

## Premise (stated; mirrored in Lean docstring)

`keys(cell) = {(o,s) : base V-flows to o at net shift s}` is
exactly the witness set the grammar's M rule quantifies over; the
channel graph realizes M's one-shared-witness quantifier. The
model is single-hop: multi-hop content movement composes through
the outer closure identically under both semantics, so the
containment/strictness statements lift hop-wise.

## What remains under pairwise cells (2026-09-15, cflow + nm-new)

With the welds gone (zero join merges), the classes that hold a
function still hold literals, heap, stack and data globals — one bag,
not per-pair leaks. Measured on cflow (channel mode, P=13; census =
classes holding a function fact / of those also holding a literal):

| configuration                                   | iteration 0 | full run  | wall (iter 0 / full) |
|-------------------------------------------------|-------------|-----------|----------------------|
| cluster mode (before)                           | —           | 2586/2497 | —                    |
| channel mode                                    | 1860/1765   | 2153/2056 | 7.5 min / —          |
| + gnulib x-allocator summaries                  | 1812/1715   | 2121/2022 |                      |
| + extern globals with their own node (flag)     | 1884/1787   | 2112/2013 | 3.8 / 10.6 min       |
| + no per-access cell identity roots (probe)     | 2424/2323   | 2787/2684 | 0.7 / 1.1 min        |
| + no X↔residue bridges (probe)                  | 1822/1725   | 2112/2013 |                      |
| P = 11 / P = 41 / P = 0 (field-insensitive)     | 1870/1720 / — / 2584/2446 | | 5 s at P=0     |

The indirect-call answer is the same in every row (42 sites, 74
pairs; cflow has one ground-truth site). Two user hypotheses were
confirmed and measured: the flows-to path sends every declared-but-
undefined global to the universal pointer (unlike PointTo.cc; now
`--cfl-ext-globals-own-identity`), and the gnulib x-allocators had no
summary. Both are real and both are small. Neither the unknown-offset
bridges nor the modulus hold the bag. What does:

1. Andersen's own width: context-insensitive formals and returns of
   generic helpers (convert_options, group_parse, xrealloc) and
   read-modify-write cycles collapsed by the SCC step. Not a device
   of ours; the user has deferred context sensitivity.
2. Identity roots for read-access cells. They are 1,222 of cflow's
   roots and 90% of the pairwise wall (7.5 min → 39 s without them),
   because every one of them is a key on every pointer loaded from
   its cell. They are also the wrong object, see below.

### Identity of unwritten content: per key, not per access

Today an identity root is minted for every cell that has no in-edge,
including the cell of every load whose pointer no store reaches
("*p" for an instruction p). Semantically the root stands for the
content the program never wrote: the external world's value. That is
a property of the LOCATION (origin, shift), not of the access. Two
loads of the same never-written field get two different roots today,
so a store through one loaded handle is invisible to a load through
the other (the identity-join ablation on nm-new lost 5 of 223
ground-truth records at reloc.c for exactly this reason: the
bfd_link_callbacks handles). At the same time each root becomes a key
of every pointer loaded from the cell and wires unrelated accesses
together (the identity-root web of the AICT attribution).

Design (premises stated; Lean: `ChannelCells.handle_*`):

- P1 (content). The content of location (o,s) is the union of the
  values stored through pointers whose plane contains (o,s), plus
  the location's initial content.
- P2 (initial content). Defined globals: their initializer (edges
  exist). Heap and stack objects: nothing — a read before any write
  is undefined behaviour and carries no function pointer of ours.
  External origins — pointees of formals with no caller, extern
  globals, wildcard results, and fields of external objects — hold
  an unknown external object.
- Rule. The unknown external object of location (o,s) is one origin
  ι(o,s), minted when the channel (o,s) is created and o is external;
  it is added to the channel's content. Fields of ι(o,s) map back to
  ι(o,s) (depth-one self loop), which keeps the set finite: at most
  one identity per external channel key. No identity is minted for an
  access cell, and none for internal origins.
- Consequences. Two loads of the same external field share the
  handle, so the store/load pair through two copies of it connects
  (`handle_flow_key_identity`); with per-access roots it does not
  (`handle_flow_per_access_fails`). Internal objects' unwritten fields
  read as empty. Identities can only key accesses reachable from an
  external object, so they cannot glue internal objects together.
- Cost. Keys per pointer drop from (owner keys + one root per
  access) to owner keys; on cflow the probe shows this is the whole
  pairwise cost problem.
- Parking. When resolution wiring gives a formal real callers, its
  identity and the identities of its channels are parked exactly as
  formal identities are parked today (rootParkable + re-admit); no
  new mechanism.

Built as `--cfl-key-identity` (74326b9). cflow, full run: wall 10:39
→ 1:38, indirect-call answer identical (42 sites / 74 pairs), 1,754
cells without a per-access root, 61 channel identities and 482 self
loops; the census equals the mint-nothing probe (2787/2684), i.e. the
per-access roots were partitions, not content. Parking of a formal's
channel identities when the formal gets callers is not implemented
yet (over-approximation only).

Gate: nm-new ground truth 223/223 with the sound rule (the probe that
mints nothing is expected to lose the reloc.c records), then the
census and cost on nm-new; then km.

### Holder-keyed object identity (2026-09-16)

The generic-container finding on cflow: every lazily created list is
one abstract object because `deref_linked_list` allocates it at one
site (`if (!*plist) *plist = xmalloc(24)`); the caller then sets
`free_data`, and every list's callback slot and every list's items pool
in that one object (static_free and free in one slot; every appended
Symbol in one `data` slot). The retrieval key of such a list is its
holder: `&sym->caller`, `&sym->callee`, a global head. Nothing else
identifies the instance.

Rule. When a fresh allocation result is stored through a pointer q
(`*q = v`, v traced to a unique allocation call through casts and
O0 spill reloads), the object stored under holder key k ∈ keys(q) is
the clone (site, k), a distinct origin with its own channels. The
base origin (site) remains the identity of the pointer v itself.

Premises:
- P3 (holder access). After the store, the program reaches the object
  through the holder, through values loaded from the holder's cell,
  or through v and its copies made before the store. There is no
  third route: an object is not addressed by anything but pointers to
  it, and every pointer to it descends from v or from the holder.
- P4 (holders do not alias by accident). Two holder keys are two
  locations; the same object is under two holders only when a pointer
  loaded from one is stored into the other, which is a copy the
  analysis sees.

Consequences and wiring:
- Stores through v (constructor-internal initialisation, uses of v
  after the store) go to the base channels (site, s), which feed every
  clone's channel (site,k,s): an a-edge base → clone per residue and
  for X. Sound: v may be any of the clones.
- Loads through v read the base channel and every clone channel: the
  read half of a cell keyed (site, s) is fed by (site, s) and by every
  (site,k,s). Sound for the same reason; clones never feed each other,
  so no content crosses holders.
- Stores and loads through a value loaded from holder k use (site,k,s)
  only: the instance is separated from every other holder's instance.
- A copy of the object's pointer stored into another holder k' is NOT
  relabelled (only the fresh-store access relabels), so the object
  keeps identity (site,k) under both holders: P4 is respected by
  construction.
- Bounds. No clone for an X holder key, for a constant-data key, or
  once a fresh-store cell has more than 32 holder keys (the base then
  receives the fact as today). A fresh-store cell whose class was
  merged by the SCC step is not relabelled either (its plane mixes
  other content).

Lean (`ChannelCells.holder_*`): in the split model a store through
holder h reaches a load through holder h' iff h = h' and the merged
model flows; a store through the base reaches the loads of every
holder; erasing holders maps every split flow to a merged flow
(removal-only relative to today).

Cost: clones are origins, so keys grow by (fresh-store cells × holder
keys), bounded above; the base→clone and clone→reader edges are one
per (clone, residue).

Built as `--cfl-holder-identity` (default off). Result on cflow
(P=13 full run and P=29 iteration 0): mechanically correct — 87
fresh-store cells, clones minted and relabelled as designed, base bit
dropped on the pre-split direct edges and the split carry — and NO
change to the census or to the static_free/.str.5 pair. Cause: the
holder pointer is already the bag. `plist` in deref_linked_list has
3,927 distinct holder origins at iteration 0, because every Symbol
pointer comes out of the hash table's `void *data` slot and every hash
table shares one bucket-array allocation inside hash_initialize (one
constructor site for all tables), so `&sym->caller` is "field of
anything". With the 32-key bound that cell gets no clones and the base
flows; without the bound the clones become holder keys of other
fresh-store cells (clones of clones), the universe grows into every
dense plane, and the run dies at 46 GB. The X holder keys, exempt from
cloning, carry the base into the X channels in either case.

Lesson: holder identity presupposes narrow holders. The container that
pollutes the holders has to be split first, and on cflow that is the
hash table: hash_initialize is rejected by the wrapper confirmer
(`table->bucket_limit = table->bucket + n`, an interior pointer of the
sub-allocation stored into the fresh object), so all tables are one
object. Order of work: (1) confirmer accepts interior pointers of a
FreshSub sub-allocation as init stores, promoting hash_initialize per
call site; (2) measure holder identity again, at P ≥ 29 so residue
collisions do not pre-pollute the holders; (3) only then decide
default-on or removal.

## Per-site accounting of one nm-new site (2026-09-17)

The user's standard for user-mode corpora: a wide answer is acceptable
when every target at a site can be explained. This section is the first
full accounting, for the site the SoK harness keys as
`elf64-x86-64.c:4221`: `info->callbacks->einfo(...)` in
`elf_x86_64_finish_dynamic_symbol`, a variadic error callback loaded from
`bfd_link_callbacks` at byte 88. The fuzzing ground truth has no record
for this line; the only callback ever installed in that slot in nm-new is
`simple_dummy_einfo` (bfd/simple.c). `_bfd_error_handler`, the other
variadic function we report, is stored only in `elf_backend_data` as
`link_order_error_handler`, a different slot.

Our answer: 51 targets. All runs below are cluster mode, exact presolve,
the nm-new summary file, P=29 unless stated.

| run | pairs | site |
|---|---|---|
| P=13 (reference) | 63,202 | 51 |
| P=29 | 63,202 | 51 |
| P=29, no X bridges (probe) | 63,202 | 51 |
| type-only candidate set (`--cfl-dump-type-json`) | 89,947 | 117 |

Every answer above is byte-identical: residue collisions and unknown-index
bridges do not decide this site or any other nm-new site. The type filter
alone would admit 117 functions here; the flow analysis removes 66 of
them, so the 51 are not the type bound.

**Where the two kinds of targets come from.** The meet trace between
`simple_dummy_einfo` and a vtable member (`binary_get_symbol_info`) has
the same shape at P=13 and P=29. The callback side: the store into
`callbacks.einfo` is a cell keyed (callbacks alloca, 88 mod P); that
class joins a 15,000-node class as soon as a pointer in that class reads
the callbacks struct. The vtable side: the initializer cell of
`binary_vec+528` (`_bfd_get_symbol_info`) joins the same class through a
read `abfd->xvec->member` by a pointer already in it. The residue partner
differs by P (528 shares a residue with 840 at P=13 and with 760 at P=29;
`bfd_target` has 107 members over 880 bytes, so some pair collides at any
P below 110) but the answer does not change because every slot that is
read anywhere by a pointer in the class enters it regardless of residue.

The per-value trace at the site (`--cfl-trace-value`) shows the three
values `info`, `info->callbacks`, `callbacks->einfo` in three distinct
classes, each carrying the same 380,430 facts: the universal pointee set.
`info` is not in any a-edge SCC (`--cfl-dump-scc` finds no cycle through
it); it is universal by propagation from its only actuals, the backend
table calls in `elf_link_output_extsym`, whose `flinfo` is the `data`
formal of the hash-table traversal callback. That formal is universal
because `bfd_hash_traverse` is wired context-free: its `data` formal is
the union of five actuals, one of which is the `bfd_link_info *info` of
`elf_x86_64_finish_dynamic_sections` itself, so every traversal callback
receives a universal `data`. A dispatch summary for `bfd_hash_traverse`
would pair callback and data per call site but cannot narrow `info`,
which is universal before it reaches the traversal.

**Why the 49 pass the type filter.** The site's call type is
`void (ptr, ...)`. `isCompatible` requires a fixed-arity callee to match
the number of actuals (3), not the call type's fixed-parameter count (1).
So every address-taken function with three pointer parameters that
reaches the universal class is admitted: `bfd_target` and
`elf_backend_data` members such as `_bfd_elf_get_symbol_info`,
`bfd_generic_lookup_section_flags`, `elf_x86_64_info_to_howto`.
Corpus-wide, 66 nm-new sites have a variadic call type; they carry 4,931
pairs, of which 4,798 are fixed-arity callees. Calling a fixed-arity
function through a variadic pointer is undefined in C, and clang types an
unprototyped (K&R) call as variadic with every actual as a fixed
parameter, so requiring `numParams(F) == fixed params of the call type`
keeps K&R dispatch intact. This rule is `--cfl-varargs-strict` (default
off; pins are measured without it).

Measured on nm-new (P=29, same flags): 63,202 → 60,742 pairs, 39 sites
changed, none looser, ground truth recall unchanged (223/223); median
width 51 → 34; this site 51 → 2. Only 38 of the 66 variadic-typed sites
change: the other 28 pass a single actual (`einfo("...")` with no
arguments), so their call type `(ptr, ...)` is byte-identical to an
unprototyped call with one pointer actual, and a fixed-arity one-pointer
callee cannot be rejected from the IR alone (about 2,300 pairs). Telling
those apart needs the source prototype, which is in the debug type of the
loaded pointer (`DISubroutineType` with a trailing null for variadic);
not built. The one non-variadic site that changed is `coffgen.c:2154`
(`bfd_coff_print_aux` through the COFF backend table in
`coff_print_symbol`), which drops from 2 targets to 0, the same site that
dropped to 0 under pairwise cells. Traced per value: in the baseline the
`abfd` formal of `coff_print_symbol` has exactly one pointee, the format
string of the einfo call at `reloc.c:8424`, because the lenient rule
admits `coff_print_symbol` (four parameters) at that four-actual variadic
call. `abfd->xvec->backend_data->_bfd_coff_print_aux` is then a read
through a string literal's content, which sits in the universal soup, and
`coff_print_aux` falls out. No instruction in nm-new reads the
`_bfd_print_symbol` slot of `bfd_target`, so `coff_print_symbol` is never
dispatched in this program: 0 is the correct answer, and the earlier
"probable soundness hole" reading of this site is withdrawn.

**Accounting of the 51.**

- 2 variadic functions: `simple_dummy_einfo` (the true target) and
  `_bfd_error_handler` (reaches the universal class through the backend
  table; a flow false positive).
- 49 fixed-arity three-pointer functions admitted only by the lenient
  varargs rule; each reaches the site through the universal class.

**What this settles.** For nm-new the per-site question reduces to two
independent facts: which functions enter the universal class (a
call-context question, settled 2026-09-14 as context-free call/return
wiring), and which of them the type filter keeps. Field residues, cells,
X bridges, allocator and libc summaries are all answer-neutral here and
were confirmed so per site, not by census.

### Why the wrong target arrives at the pointer (2026-09-17, cluster mode)

A type rule only says which arrivals were wrong. The user's question is
how `binary_get_symbol_info` reaches the einfo pointer at all. Three
instruments answer it, all P=29, cluster mode:

- `--cfl-trace-func=<root>` arrivals now carry `key=(o,s) by-ptr=<class>`
  on join-triggered merges: the pointer class whose cell sweep issued the
  join. `scratchpad/chainid.py` walks a class id back to the seed within
  one solve iteration.
- `--cfl-dump-merges=<tsv>` writes every union of the final solve with its
  cause (join key and issuing pointer, or SCC collapse) and a node-name
  table with presolve-class aliases. `tools/merges.py LOG X Y` replays it
  and names the first union that put two nodes in one class.
- `--cfl-dump-scc` and `--cfl-dump-class` now match member names, so a
  node folded into a presolve class or an earlier merge is addressable;
  the cycle search skips a merged class's own self-loop.

The chain, oldest hop first:

1. The function root is seeded into the initializer cell of
   `binary_vec+528` (`_bfd_get_symbol_info`). Correct.
2. Union 11,639 of 22,601 joins that cell's cluster, key
   (`binary_vec`, 528 mod 29), into the universal cell cluster U. It is a
   cell-sweep join issued by the class holding `section`, the `asection *`
   formal of `_bfd_generic_link_add_one_symbol` (reload at linker.c:1394):
   that class held the fact (`binary_vec`, 6) and its dereference cell was
   already in U (it had joined U at union 6,158 under a string-literal
   key, issued by the same pointer).
3. The einfo load's cell is in U, so the load's class gets the root by
   one a-edge.

Why `section` holds a `bfd_target` fact: `section` is in U itself,
absorbed by the a-SCC collapse. The shortest a-cycle through it at the
first collapse has four hops: the formal → its reload → a cell cluster
(rep: the buffer allocated at cofflink.c:721, holding the hash entry's
`u.def.section` and the symbol's `section` slots) → the load `p->section`
at linker.c:1167 in `generic_link_add_symbol_list` → the actual of the
next `_bfd_generic_link_add_one_symbol` call → the formal. A value that
is stored into a cell and loaded back from it has exactly the cell's
facts, so collapsing the cycle is exact; the damage is that the cell
cluster is coalesced: cluster mode joins cells of different keys whenever
one pointer holds both keys, and U holds `binary_vec` legitimately
through the `xvec` cells of bfd objects (`abfd->xvec = *target`,
format.c:289). The section-flow recursion (hash entry slot ↔ symbol slot)
then carries all of U's content into every `asection *` value, whose cells
join every cluster keyed by those facts, which is step 2.

So, for this site: the mechanism is key-cluster coalescence through
multi-key pointers plus context-free formals, entered through the
section-flow recursion of the generic linker. The pairwise-cell mode
reached the same 51 targets by a route not yet traced with these tools.

## Single-site query and the widening report (2026-09-18)

`--cfl-demand-site=<file:line | function>` turns a run into a single-site
query: only the matching indirect-call sites seed demand relevance
(`--cfl-channel-demand`) and lazy-mint relevance, and at the end of the
solve a widening report walks the fact flow backward from the site's
callee operand. Answers for other sites are not valid in this mode.

The report builds the reverse fact-flow graph over classes with four
edge kinds: `a` (assignment), `f` (field), `o` (owner hop: a cell's keys
are the facts of its owner pointer) and `x` (VX bridge). Fact counts are
R plus RB (bridged facts land in RB; a load re-emits them as native).
The slice is condensed into strongly connected components; a widening
component has at least twice the facts of every input component. The
spine walks from the operand's component to the largest input until the
first widening component, then dumps every member class that receives an
edge from outside (the entries), with the external in-degree by kind.

nm-new, cluster mode, iteration 0, site elf64-x86-64.c:4688 (74 targets,
all through the universal set; the enclosing function has no direct
caller). The operand is one `a` hop from a single widening component:
9,143 classes, 23,115 members, 271,352 facts, 8,500 input components of
which 8,341 carry fewer than 16 facts and the largest carries 1,860
(0.7%). Entries: 127 formals of 108 functions (610 call edges; bfd_seek
arg0 64, bfd_get_section_by_name arg0 52, bfd_bread arg2 45, bfd_bwrite
arg2 39, bfd_malloc_and_get_section arg0 26, bfd_release arg0 21), the
merged cluster class (1,848 stores, 5,777 owner pointers), 94 cells, 92
loads. So for this site universality is not inherited from any input: it
is produced by one cycle closed by generic `bfd *`, `asection *` and
`void *` formals and by cluster-joined cells, and fed by thousands of
tiny inputs. This is the per-site form of the leak-point result: no
single input matters, the cycle does.

cflow, lazy demand, site wordsplit.c:2374: 21 relevant nodes, answer
identical to the all-sites run (6 targets), spine load, read half,
channel, cell with 6 stores, global.

## Delta debugging: the 18-function reproducer and the exact-model verdict (2026-09-19)

tools/dd-funcs.py runs ddmin over function bodies (`--cfl-ablate-funcs`,
monotone: an ablated body emits no flows, callers still wire formals)
with the property "site elf64-x86-64.c:4688 has a target outside the 11
that slot 103 and its bucket-7 neighbours of the 19 target vectors can
deliver". From 1,693 functions, 1,294 tests (6 in parallel, 10 s to
2 min each) reached a 1-minimal set of 18 bodies that still gives 71 of
the 74 targets: the site function, nm's display_file and
display_archive, bfd_openr, bfd_fopen, bfd_find_target,
bfd_openr_next_archived_file, bfd_get_section_contents,
bfd_get_full_section_contents, bfd_get_reloc_upper_bound,
bfd_generic_get_relocated_section_contents, and seven generic linker
routines (_bfd_generic_link_add_symbols, _bfd_generic_link_add_archive_symbols,
generic_link_add_object_symbols, bfd_generic_link_read_symbols,
_bfd_generic_link_output_symbols, _bfd_generic_final_link,
default_indirect_link_order). bfd_check_format_matches is not needed.

On the same reproducer the exact model (lazy addresses, channel cells,
demand) converges in 8 seconds with 8 relevant nodes and gives 0 targets
at the site, which is the flow-insensitive, context-insensitive truth at
iteration 0: the site function has no callers, so nothing is ever stored
under its bfd's xvec key. Cluster mode gives 71. The site's width is
therefore entirely cluster-mode coalescence, not program semantics.

The traced chain for one wrong target (_bfd_archive_close_and_cleanup)
in the reproducer: global → slot 31 of i386_pei_vec → merged with slot
89 of the same vector (272 ≡ 736 mod 29, bucket collision) → merged
with slot cells of every other vector by key (i386_pei_vec, s11) issued
by the BFD_SEND slot access in bfd_generic_link_read_symbols, whose xvec
pointer holds all vectors (transitive key coalescence at a context-free
helper) → merged with the *elf64_x86_64_bed backend-data cell by a key
whose object is the function _bfd_bool_bfd_false_error (a function
root used as a key once slot contents flowed into the xvec-holding
class) → VX bridge into the exact slot-103 cell of x86_64_elf64_vec →
the site's load. Four model mechanisms, no program mechanism.

## Delta debugging over the exact model: the 46-function reproducer and the bulk-memcpy fix (2026-09-22)

The exact model (byte-exact lazy addresses, write/read cell halves,
demand wiring) removes the site's cluster-mode width, but its full
nm-new run is slow because a few pointers hold thousands of address
keys (the hash-table bucket cell, the stabs and eh_frame byte writers,
char* locals). A second delta-debugging run used that as the property:
keep a subset of function bodies (all others ablated) such that the
single-site exact solve still has a cell with more than 5,000 keys.
Plain ddmin stalled at 72 functions because 26 of them were removable
one at a time but ddmin removes one per round; a greedy step that
first tries the union of the individually-removable functions (still
verified by a test) brought the set to 46 in one step, and that set is
1-minimal.

The 46 functions are the bfd hash-table core (init, lookup, insert,
the entry constructors), section lookup and creation, the link-hash
helpers, stabs and merged-section handling, ELF symbol and relocation
reading, and the i386 and x86-64 check_relocs and relocate_section.
The widest pointers there are the link-hash entry `h` and the section
`sec` in relocate_section and elf_link_output_extsym, with about 5,900
facts: string literals, the std-section array, the global symbol
array, and thousands of synthetic objects. These are single-member
classes with no merges: the width arrives by flow, not by class union.

Tracing one string literal back from `h` (first-arrival trace and a
chain walk) gave the route: the literal is the name of a std section;
it is read as the content of that section object by the as-needed
rehash loop in elf_link_add_object_symbols, `memcpy (old_ent, p,
entsize)`; the memcpy fallback for variable-length copies aliased its
two pointer arguments bidirectionally, so every hash entry `p` became
an alias of the scratch buffer and the buffer's contents (strings,
next pointers, and through an integer path even a constructor's
address) flowed into entry pointers, from there into the sym_hashes
array, and into `h` in check_relocs and relocate_section.

A copy never makes its destination point where its source points, so
the alias was not needed for soundness. Under flows-to the fallback is
now a directional content move: the wildcard on each pointer makes the
existing deref-to-deref edge read every cell of the source objects and
write every cell of the destination objects. On the reproducer the
top cell fell from 5,537 to 3,516 keys and the solve from 560 s to 264
s; on the full cluster-mode nm-new run pairs went from 44,695 to
44,691 with recall unchanged at 207/223 and wall time from 3:24 to
2:04. The smoke suite passes. Commit 3cc90e8.

After the fix, `h` in elf_link_output_extsym still holds 4,865 facts
of the same mixture. The identity-join ablation probe collapses it to
3 facts, the channel graph from 6,572 nodes to 58, and the solve to
16 s, but that probe removes every join whose key origin has no value
or is an instruction, which includes all allocation-site objects, so
it is an upper bound on what heap-keyed flow carries, not an
attribution to identity roots. Denying external identity to the
callerless formals of non-entry functions (`--cfl-closed-world=main`,
884 formal classes on the full run, 95 on the reproducer) changes no
number in either the cluster run or the reproducer, so the formal
identities are not the residue either. On the full cluster-mode run
the probe removed 5,180 pairs and 20 true targets. The next traced chain crosses functions only through
identity-keyed cells: a section's map_head read in elf_link_sort_relocs
is stored into another section's map_tail whose cell is keyed by an
identity root minted in elf_link_add_object_symbols, and from there
reaches `h`. The open design question is the one already noted in the
join code: witness-gated identity joins or an object-indexed cell
model.

### Key identity was off in every nm-new run (2026-09-22)

`--cfl-key-identity` defaults to off and none of the nm-new scripts
passed it; lazy-address mode only turned on channel cells. So every
cluster and exact-model number since the 18th, including the two
multi-day exact runs, was taken with per-access identity roots, the
model the section above replaced. The join-ablation census on the
reproducer showed it directly: 622 of the ablated key origins were
value-less cells `*fn::gep@N`, the per-access roots.

With key identity on:

| run | before | after |
|---|---|---|
| 46-function reproducer, solve | 268 s | 96 s |
| reproducer, channel nodes | 6,572 | 3,566 |
| reproducer, widest cell (keys) | 3,516 | 1,584 |
| reproducer, `h` in elf_link_output_extsym (facts) | 4,865 | 2,575 |
| reproducer, classes mixing functions and literals | 1,624 | 0 |
| cluster all-sites nm-new, pairs | 44,691 | 42,582 (61 sites tighter, none looser) |
| cluster all-sites, recall | 207/223 | 207/223 |
| cluster all-sites, wall / RSS | 2:04 / 8.5 GB | 1:32 / 3.9 GB |

Channel cells now default key identity on (`--cfl-key-identity=false`
restores per-access roots). In cluster mode, which has no channels,
the flag mints no content identity at all, so it stays opt-in there.
What remains on the reproducer after key identity is the hash-lookup
transport (`*bfd_hash_lookup::load@488`, 1,565 keys), the
elf_link_add_object_symbols loads and the stabs byte writer: the
context-free helper returns, which the per-caller summary direction
addresses. A closed-world rule for callerless formals (formals of
non-entry functions hold no external object) was built and measured:
it changes nothing on the full runs, and leaving such formals rootless
breaks indirect-call wiring (recall 80/223), so it was removed. The
identity-join ablation probe classifies allocation-site objects as
identity too, so its collapse of `h` to 3 facts was an upper bound on
heap-keyed flow, not an identity attribution.

## Reachability-driven body processing (2026-09-23)

A flows-to graph assumes every instruction executes. Formals are the
one conditional place (no caller, no actual-to-formal edge), but a
body's sources are not: the function and global addresses it passes as
arguments, its allocation sites and its literals enter the graph
whether or not the function is ever called. In nm-new the ELF final
link is never invoked, yet bfd_elf_final_link's traverse call hands
elf_link_output_extsym to bfd_hash_traverse, and the callback site
hash.c:657 answers with four linker callbacks the program can never
call there. The pass visited all 1,396 bodies up front.

`--cfl-reachable` processes a body only once the function is reached:
from the entries (`--cfl-entry-list`, one name per line; default
`main` plus `llvm.global_ctors` and `llvm.global_dtors`) by direct
calls and by summary callback bindings, transitively; at indirect-call
wiring, before the callee's formals are wired, as sites resolve; and
by escape, when a function constant is passed (possibly through
select, phi or a constant expression) to a callee that has no
definition in the corpus, since the outside may call it with arguments
we never see. Bodies processed after the first solve enter the next
solve exactly as wiring edges do: each resolution pass rebuilds the
dense graph from all edges. The wiring loop iterates a snapshot of the
indirect-call sites because new bodies add sites. Unreached
address-taken functions are ledgered at every pass as candidates for a
missing entry. The mode needs the multi-pass fixpoint: with
`--cfl-flows-to-max-iters=1`, the single-pass configuration of the
nm-new pins, sites reached only through resolution are never solved
(191 pairs, recall 43/202, not a bug).

Entries for the other corpora: a library's interface is its defined
functions with external linkage and default visibility after the
version script, plus the fuzzer entry; the kernel's outside callers
are assembly and hardware, so its entries are the functions assembly
calls (the undefined symbols of the `.S` objects, `asmlinkage` and
`__visible`), `start_kernel` and `start_secondary`, plus
`EXPORT_SYMBOL` when modules count as outside callers. Everything else
(syscall table, initcalls, IRQ actions, work items, timers, kthreads)
is reached from those through C dispatchers the graph already models.

nm-new, cluster configuration, full fixpoint:

| | baseline | reachable |
|---|---|---|
| resolution passes | 4 | 5 |
| bodies processed | 1,396 | 1,381 of 1,693 defined |
| address-taken never reached | | 18 (iovec of bfd_openr_iovec, mmap paths, from_remote_memory, a select-passed qsort comparator before the escape rule) |
| pairs / recall | 63,200 / 223 | 63,200 / 223, byte-identical |
| wall / RSS | 12:36 / 10.8 GB | 11:25 / 10.8 GB |

Identical answers because in cluster mode the link-add-symbols slot
call at simple.c:259 resolves to 115 targets including
bfd_elf_final_link (same function type, slot offsets collide under the
buckets), which makes the whole linker reachable. Whether the linker
falls out under exact addressing is what the single-site exact query
for simple.c:259 decides; the exact single-site run for site 4688 with
key identity, reachability and the multi-pass fixpoint is running.

### Correction: the single-pass exact-model answers are unsound (2026-09-24)

The exact-model single-site runs were configured with
`--cfl-flows-to-max-iters=1 --cfl-iter-cap-ok`, the single-pass
setting of the cluster-mode pins. The corrected single-site run for
elf64-x86-64.c:4688 (key identity, 30 h, 16 GB) answered 0 targets;
the ground truth records `_bfd_elf_get_dynamic_reloc_upper_bound`
there and the cluster answer contains it. The log says why: the
fixpoint hit the cap with 13,664 newly wired pairs unprocessed. The
site's function, elf_x86_64_get_synthetic_symtab, is reached only
through the get-synthetic-symtab slot call at nm.c:1159; that pair is
wired at the end of the single pass and never solved, so the formal
`abfd` holds only its identity root, the slot cell reads as its
content identity, and the answer is empty. Scored over all sites the
single-pass exact answer set has recall 76 of 223; an earlier one had
14 of 223. Cluster mode at a single pass still answers such sites
because key coalescence carries the true target along with the soup.

So the verdict of the 18-function reproducer, exact 0 against cluster
71, compared a recall failure with a precision failure. Every
exact-model number in this document taken from a single-pass run is a
lower bound on the answer, not the answer. A fair comparison needs the
multi-pass fixpoint on both sides: cluster mode converges in four
passes at 63,200 pairs and 223 of 223; the exact all-sites run with
key identity and reachability is the corresponding measurement and is
in flight. The two remaining single-pass exact runs, four and a half
days in, will produce unsound answers when they finish.

### The link-add-symbols slot is not a bucket collision (2026-09-24)

The single-pass exact query for simple.c:259 (key identity, 33 h)
answers exactly the same 115 targets as cluster mode, including
bfd_elf_final_link, so the earlier explanation for that site, slot
offsets colliding under the buckets, was wrong. The spine shows the
mechanism: the callee operand, with 75,277 facts, is read from
`abfd->xvec` through a channel keyed by the content identity of the
formal `output_bfd` of `_bfd_x86_elf_always_size_sections`, an
unrelated linker callback, and that channel's content is the
universal widening component. In a single pass every callback formal
is callerless and holds an identity root; the identities of different
callbacks meet in shared helpers; a slot read through such a channel
sees everything ever stored through any holder of that identity. Both
answers of the single-pass exact model are therefore wrong in opposite
directions: empty at 4688, the full soup at 259, and for the same
reason.

This also says what reachability mode buys beyond dead code. A
callback's body is processed when its call site resolves, with the
actual-to-formal edges already present, so the next rebuild mints no
identity root for it; plain multi-pass mode mints those roots at pass
zero and never parks them. The comparison that decides it is the
exact all-sites run with key identity and reachability against the
exact multi-pass single-site run for 4688 without reachability, both
in flight.

## The BFD_SEND dispatch: constant channels, identity welding (2026-09-25)

The junction ranking of the site-4688 widening component (commit 7e697f4)
put the union at the BFD_SEND dispatch: 16 target-vector slot functions,
each with 105 internal in-edges from one formal class, each with 12
return edges out. The 105 edges are the `abfd->xvec->slot` and
`abfd->iovec->op` reads. The obvious reading was that the slot cells of
the constant target vectors coalesce (one wide read cell merges the 19
keys `(vec_i, s)` into one cluster, a second read of another slot in the
same bucket joins it, and every dispatch site resolves to every slot
function). That reading was tested and is wrong. This section records
the test, the mechanism that actually carries the width, and the cost of
removing it.

### Constant globals as channels (`--cfl-key-channels`, default off)

The target vectors, the iovecs and the vector table are LLVM `constant`
globals with pointer content: 101 of them in nm-new. Nothing can store
into them, so their memory holds exactly their initializer, and a key of
such an object has nothing to gain from a cluster (a cluster unifies the
store cells and load cells of one location; a constant location has no
store cells). The flag treats those keys the way the exact model treats
every key: `joinCluster` pends them instead of merging, and the barrier
flush wires one channel node per key. Writers are the initializer cells
only (`CallGraphPass::constInitCells`, recorded in `processInitializer`;
1.59 M store cells whose pointer may point into a constant were not
wired: constant memory cannot be written, and wiring them would pour the
universal cluster into the channel). Readers are served through a read
half per class: a solver node holding a copy of the class's loads
(out-edges to nodes below N, field edges, nested cells), fed by the
channel, never feeding one. The half follows the class through merges
(the loser's loads are appended to the keeper's half and the half's
content is pushed along them; the loser's half keeps serving the
loser's keys, whose marks are dropped and re-offered). Channel keys
join on native facts only; read halves and channels are memory nodes
for the a-SCC collapse.

Three versions were needed, each falsified by a 16-minute run:

1. Channel into the reader cell itself (no half): byte-identical to the
   baseline. The reader cell is also a member of the mutable clusters
   its pointer reaches, so it carried the slot functions into the
   universal cluster: the conduit.
2. Read half keyed by the raw cell, with any cell with in-edges as a
   writer: recall 28/223. Cluster mode keeps its "already joined" marks
   per class and deduplicates cell lists to class representatives, so a
   key pended by one member of a merged class was never pended for the
   others and their halves were never made (bfdio.c:211 lost
   `cache_bread` while the same site kept `memory_bread`).
3. Per-class read halves as described above. Sound: bfdio.c:211 has
   `cache_bread` again, fixpoint answers byte-identical to the baseline.

Measurement (nm-new, cluster fixpoint, 29 field buckets, same machine):

| run | pairs | recall | site 4688 | simple.c:259 | hash.c:657 | wall | RSS |
|---|---|---|---|---|---|---|---|
| baseline (clusters) | 63,200 | 223/223 | 74 | 115 | 4 | 12:36 | 10.8 GB |
| constant channels | 63,200 | 223/223 | 74 | 115 | 4 | 27:57 | 11.1 GB |

Iteration 0 resolves 1148 icalls / 58,976 targets against 58,978: the
two targets removed are the only effect. The constant slot cells are not
the carrier of the width. The flag stays off by default.

### What carries the 74 targets to site 4688

`--cfl-trace-value=elf_x86_64_get_synthetic_symtab` on a single pass
dumps the fact count of every pointer value in the function holding the
site (IR: `%46 = load abfd; %47 = gep %46, xvec; %48 = load %47;
%49 = gep %48, slot 103; %50 = load %49; call %50`):

| value | facts |
|---|---|
| `abfd` formal (arg0), `%46`, `%47` | 1 (a synthetic identity root, r10124) |
| `%48 = abfd->xvec` | 235,860 |
| `%49`, `%50` (the callee) | 235,860 |
| `bfd_get_section_by_name(abfd, ...)` result | 235,860 |

The function is a target-vector slot (`_bfd_get_synthetic_symtab`),
reached only through BFD_SEND. In the pass its formal has no wired
caller, so it carries only its identity root. The load `abfd->xvec`
reads the key `(r10124, s_xvec)`, and its cluster holds the whole soup.
The identity r10124 is passed as the actual of the very call at the
site (`%50(%51)`, `%51 = abfd`), so it flows into all 74 candidate
callees; in each of them `abfd->field` cells join keys `(r10124, s)` and
are merged with whatever else those cells' pointers reach. The identity
of one unwired formal is a universal key: every function it flows into,
over-approximated callees included, has its field cells welded into one
class per bucket. The 74 targets are the bucket-103 content of that
class; the same mechanism produced the `section` formal chain of the
2026-09-24 note and the formal-confluence glue of the kernel tcp/ahci
weld. It is self-reinforcing: the wider the answer at the site, the
more callees receive the identity.

### Identity roots as channels (`--cfl-identity-channels`, default off)

The same machinery with identity roots (14,782 of 20,872 roots in
nm-new: classes minted only because they have no in-edge, plus extern
globals) as channel keys, stores through the identity being the
writers. Correct on the small reproducers (scratch `cc/vt{,2,3,4}.c`,
including a callee reached only through the dispatch), and exactly the
exact model's treatment of external origins. On nm-new the first drain
never reaches a flush: 16.8 G facts and 46 GB after 10 minutes (killed;
the baseline never prints a progress line, its drains stay under 1 M
pops). Unwelding the identities gives the unmerged closure of the exact
model, and the merged planes of the welded classes were what kept
cluster mode at 10 GB. The width and the speed of cluster mode are the
same thing.

### Where this leaves the fix

The imprecision at the dispatch sites is the identity of an unwired
formal acting as a key while the formal is at the same time being passed
into the functions the site resolves to. Two directions remain, neither
implemented tonight:

- Do not let an identity root serve as a join key at all: a load
  through a callerless formal reads nothing but a fresh identity (the
  exact model's key identity), and stores through it are dropped from
  keying. Sound only across the outer fixpoint (the formal gets real
  actuals once its callers are wired, which is why single-pass exact
  answers were declared unsound on 2026-09-24), and the fact volume of
  the unwelded closure has to be paid somewhere.
- Park the identity when the formal is wired (noted in memory as not
  implemented): the identity then stops seeding across the newly wired
  edges, and the welding it caused in earlier passes must be undone,
  which the incremental solver cannot do without a rebuild.

### Carving census (`--cfl-census-carve`, 2026-09-26)

The archive block of the previous section (`bfd_zmalloc` of `struct
areltdata` + `struct ar_hdr`, archive.c:1868) is the program acting as
its own allocator: one block, two objects, told apart only by offset.
Arena allocators look the same from outside. The census asks how common
that is. For every allocation call (the `FRESH` summaries), it follows
the result inside the function through alloca slots, GEPs, casts, phis
and selects, keeping the byte offset from the allocation; a struct-typed
GEP applied at offset o types the range [o, o + sizeof S). The type at
offset 0 is the object's type T. A typed use at or beyond sizeof T is a
carve unless an array of T explains it (offset mod sizeof T is 0 with
the same type, or lands on a member of T of that type, nested members
included). Variable-index derivations, the wildcard producers, are
counted per site with the range they start from. Reporting only.

nm-new: 540 allocation sites, 76 with a constant size. 165 have a struct
type at offset 0, 375 have none inside their function (byte buffers, and
wrappers that return the block: `bfd_malloc_and_get_section` and the
like; typing those needs the callers' uses), 14 have several types at
offset 0. 28 sites are arrays of the offset-0 type. Two carves:

- `bfd_ar_hdr_from_filesystem::call:bfd_zmalloc@1868`: `areltdata(56)
  +56:ar_hdr(60)`. The genuine one.
- `coff_get_normalized_symtab::call:bfd_zalloc@1821`:
  `coff_ptr_struct(56) +64:internal_syment(40)`. A false positive: the
  member at +8 is an anonymous union, which LLVM lowers to its largest
  member (`%union.anon.14 = { %union.internal_auxent }`), so the
  `internal_syment` view never appears in the layout. Unions are the
  blind spot of layout-based typing.

So carving is rare in libbfd once the arena allocators are summarized
(`bfd_alloc`, `bfd_zalloc`, `bfd_hash_allocate` are `FRESH`; had they
not been, `_objalloc_alloc` would be the carve). The wildcard producers
are elsewhere: 25,555 variable-index derivations at 153 sites, led by
byte-buffer parsing (`do_slurp_bsd_armap::call:bfd_zalloc@971`, 3,333
derivations, untyped) and typed arrays (`bfd_symbol[i]` in
`_bfd_x86_elf_get_synthetic_symtab`, 802). The first is the typed-store
lever (byte stores of pointer-free values should not put a block on the
wildcard plane); the second is the strided address the lazy model
already has. Bounded sub-object ranges would matter for one site here.

### Field-insensitive channels, and the array extent bound (2026-09-26)

A channel-cell run of nm-new with no field model at all (`--cfl-channel-cells
--cfl-field-buckets=0`, key identity, multi-pass) gives 63,203 pairs,
recall 223/223, site 4688 = 74, simple.c:259 = 115, hash.c:657 = 4 in
25:48 and 2.1 GB. Cluster mode at 29 and at 137 residues gives 63,200 and
the same site answers; the exact model at pass 1 (demRA) averages 56
targets per site against cluster mode's 61. Not unifying changes nothing
on nm-new, and residues change nothing: every model reads the dispatch
tables field-insensitively at the same instruction,

    BFD_SEND_FMT (abfd, _bfd_check_format, (abfd))            format.c:322
    %206 = getelementptr [4 x ptr], ptr %198, i64 0, i64 %fmt

The field-insensitive model returns the whole vector by definition; the
cluster puts the variable index on the wildcard plane, which bridges to
every residue; the exact model minted a strided address (offset 264,
stride 8) whose overlap test ignored bounds ("conservative"), so it met
every 8-aligned slot at or after 264: about 75 of the vector's 107
slots, for each of the 19 vectors. The signature filter then trims the
thousand functions read to the 74 and the 115.

The bound: a lazy label carries the extent of the array a variable index
steps inside (element count from the GEP's indexed array type, times the
element size; 0 for a pointer-level index or an unknown count), the
address descriptor carries it, a member step off a strided address
shifts the family and keeps the extent, two strided steps still widen to
the range, and `addrOverlap` stops at the extent. Sound under C's own
array bound (no out-of-bounds indexing). Measured: a micro test with an
array of two slots followed by two more function pointers reads only the
two; the 46-function exact reproducer of the universal pointer at site
4688 resolves it to nothing (correct for that slice), with addresses
12,679 → 7,684, range addresses 716 → 231, overlap bridges 10,933 →
6,252. Unification bought nothing on this program and cost memory
(10.8 GB against 2.1 GB without it); the width was the tables' arrays.
