# Lazy addresses: exact byte offsets as facts, materialized on demand

Status: DESIGN 2026-09-17 (user's v2 of 2026-09-14, "lazy expansion upon
GEP"); implementation behind `--cfl-lazy-address` on top of channel mode.

## Premises (stated; to be mirrored in Lean)

P1. A pointer fact names an address, (object, byte offset), not (object,
    offset mod P). Two accesses alias iff their address sets intersect.
P2. Storage identity is the address: the content stored at (o, e) is one
    node; a load through a pointer reads the nodes of the addresses the
    pointer may hold. No per-pointer cell, no cluster join, no residue
    channel: the join/cluster/channel machinery of the residue design is
    a workaround for offsets that were not exact.
P3. A GEP with constant indices is an exact remap e -> e + k. A GEP with
    one variable array index over an element of size s > 1 is a strided
    address {b + s*i : i >= 0}, kept as (o, b, s). Two variable indices,
    or byte arithmetic (s = 1), give the object's range wildcard (o, X).
P4. Addresses are minted only when reached: the fact universe grows with
    the offsets the program actually forms, not with |objects| x P.

## Encoding on the existing solver

- Facts stay bitsets over root ids; the shift dimension collapses to one
  plane (NSHIFT = 1). Each address (o, e | (b, s) | X) is a root id with
  a descriptor; object roots are (o, 0). Function and identity roots are
  not addresses and never remap.
- f-edges carry an exact label (interned {offset, stride}) recorded per
  edge out of band; the grammar's residue labels are untouched. Label
  index 0 is reserved for offset 0 so the SCC collapse's "residue-0 f
  edge" test keeps its meaning.
- Propagation over an f-edge is a per-bit memoized remap instead of a
  plane rotation: exact + k -> exact; strided + k -> strided (base + k);
  strided step on exact -> strided; strided step on strided -> X; X -> X.
- Wildcard (fx) classes mint (o, X) for every object they hold.
- Channel keys are address roots. When a channel is created for an
  address of object o it is bridged (fact exchange, as the VX bridges
  were) with every existing channel of o whose address set overlaps:
  X overlaps everything; exact e vs strided (b, s): e >= b and
  (e - b) mod s = 0; strided vs strided: (b2 - b1) mod gcd(s1, s2) = 0
  (bounds ignored: conservative).
- Constant data-only objects never anchor channels (existing rule).

## What is deliberately not changed

- Context: formals stay shared. This design fixes the object and field
  dimensions only (2026-09-14 note); the coupler census shows the nm-new
  cluster is call-context confluence plus per-pointer cell fusion, and
  this design removes the second.
- Unknown-layout memcpy keeps the wildcard fallback (both sides X).
- Batch, incremental, bidi-prune and the closure verifier refuse the flag.

## Gates

1. Micro suite (test/t_*.bc) + cfl-smoke byte-identical with the flag off.
2. cflow: 17/17 GT; nm-new iteration 0 vs cluster iteration 0 (44,695
   pairs) and vs the pairwise iteration-0 run.
3. Per-site: the einfo site's chain under lazy addresses.
