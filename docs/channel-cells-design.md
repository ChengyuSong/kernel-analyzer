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
