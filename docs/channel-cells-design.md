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
