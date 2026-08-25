# Rendezvous-Cell Keying — Design Frame (Gate-0 in progress)

The campaign every 2026-08 measurement forces: split the weld cells by
container instance. Status: Gate-0 sizing census running (km, fs
all+ids + adoption + chain, `--cfl-census-couplers
--cfl-probe-blob-formation`); this doc frames the design space so the
census output drops into a decision, not a debate.

## Why (the forcing chain, all measured)

1. One giant: all fat sites read the same pool (5.18: R[giant] exactly;
   6.18 fs: 7,767-fn core at every fat caller).
2. No downstream lever pays first: origin-split D==1/0.000%;
   witness-read == pooled; adoption tail-flat at FI.
3. The welds are named cells (socket/VFS attributions): bus klists,
   `inode_hashtable` chains, syscall demux allocas, infra globals.
4. The kernel's own key at those cells is the container INSTANCE
   (docs/kernel-id-keys.md), and instance partitions track subsystems.
5. Free rider: the `match()`/`d_compare` registry-probe idiom resolves
   exactly once instances split (the predicate lives on the key
   object).

## The mechanism problem

The solver's join rule: values stored into the same (origin, shift)
cell key join their classes, and union-find makes joins TRANSITIVE
across keys through shared members — the deliberate over-approximation
that builds the giant. Instance keying cannot be applied at the generic
frame (at `bus_add_device` the owner class is already pooled — the
instance identity is gone by the time the cell is touched; same
dependency trap as every failed lever).

## Design axes (the census picks the point)

**A. Eligibility — which cells get keyed.** A join whose KEY ORIGIN is
a recognized container-instance global (bus_type / class / chain-head /
hashtable-head per the id-keys taxonomy) is instance-anchored: distinct
instance origins = distinct sub-keys, never merged with each other.
This is decidable at the join (the key origin is already in hand) and
needs no generic-frame provenance. Cells whose key origin is NOT an
instance global keep today's semantics.

**B. Attachment discipline — reuse, don't invent.** The non-transitive
bridge machinery already exists and is proven twice: rodata copy-not-
unify (task #25: writer joins merge, reader joins attach via bridges,
mixed cells demote soundly) and join-cone (#38). v0 is "copy-not-unify
for instance-owned container cells": same-instance writer joins merge
(one instance's pool — the kernel-correct granularity), cross-instance
transitivity through shared members is cut by bridging instead of
merging. New code is the eligibility class + certification, not a new
solver discipline.

**C. Scope — census-contingent.**
- Short head (a dozen cells carry the giant): enumerate the eligible
  instance families explicitly (bus/class/chain/hash heads), gate each
  like a channel. Bounded campaign, tracepoints-style.
- Long diffuse tail: eligibility must be generic at the join rule
  (any join keyed by a global with >1 same-typed sibling global?) —
  bigger blast radius, needs the L1-assertion + Lean treatment that
  batching got.

## Soundness obligations

- A load whose base cannot be resolved to one instance reads the UNION
  of sub-cells (pooled fallback, LEDGERed) — never fewer.
- Mixed cells (instance-keyed cell also fed by unkeyed writers) demote
  to pooled, loudly (the #30 demotion rule).
- Interaction with severed registrations (chain prover): channels
  remove pool feeding; keying must not assume channel coverage.
- Exactness claim to machine-check: keyed closure ⊇ every derivation
  of the unkeyed closure that does not cross distinct instance keys;
  crossing derivations are exactly the removed set (the certificate).

## Gate-0 verdict (2026-08-24, km 6.8.2 fs all+ids + adoption + chain)

520 cross-subsystem welds / 48,579 merges over 63 subsystems; blame is
now fully named (unnamed-formal fix). **The head is SHORT — but
heterogeneous.** Ranked by subsystem span (the giant-forming metric;
event counts are small because a weld fires once and transitivity does
the rest):

| weld family | span | mechanism class |
|---|---|---|
| `__traceiter_task_newtask::load` (tracepoint arg pooling) | 53 | part SEMANTIC FLOOR: all tasks are one population by kernel semantics; the excess is what rides transitively through task field cells |
| `proc_dostring::arg0` + sysctl handler formals | 56 | NEW FAMILY: every subsystem's static `ctl_table` global flows into shared handler formals; `table->data` points into subsystem variables — instance-keyable (tables are named globals) |
| `<synthetic>/join` residue | 58 | needs one more naming hop (assistant-node keys) |
| task-adjacent formals (`copy_process::arg3`, `delayacct_add_tsk::arg0`) | 3-9 | task nexus, same floor caveat |
| everything else | 2-4 | locally contained, not giant-formers |

Plus the slice-study inventory (drivers corpus): bus klists,
`inode_hashtable` chains + LSM formals, sockfs embedded inode,
socketcall demux allocas, infra globals (timekeeper/rcu/tick).

**Scope decision: A-list (option 1).** Campaign order by mechanism:
1. sysctl `ctl_table` instance channel — cleanest new win: tables are
   static named globals, registration is a walkable idiom
   (tracepoint-keys shape), span 56.
2. Driver-core container cells (klist) — instance keying proper, the
   drafted mechanism.
3. Socketcall demux + `__warn`/print args — sink/solved-summary
   treatment, not keying (cheapest; printf-vararg-sink precedent).
4. Tracepoint-arg keying — LAST and carefully: per-tracepoint arg
   granularity already exists; the residual task-pool weld is partly
   semantic floor. Measure the floor (population census) before
   building anything.
5. `inode_hashtable` — park until the sb-instance question is designed
   (sbs are mount-dynamic; static ceiling may be per-fs-type).

## Item-2 exploration: klist keying (2026-08-25) — REORDERED

Three findings, two of them structural:

1. **The klist containers are not cells of the instance globals.**
   `bus_register` allocates ONE `subsys_private` for every bus
   (drivers/base/bus.c:787) and `device_private_init` ONE
   `device_private` for every device (core.c:3249). The container
   cells (`klist_devices`/`klist_drivers`) live on a single shared
   heap origin; the static `bus_type` global only holds the `->p`
   pointer. Instance-keying those cells therefore REQUIRES per-bus
   heap identity first — allocation-context cloning at `bus_register`
   anchored on its constant bus argument (FRESHSUB-shaped, but the
   body has kset/kobject pointer effects a summary would sever).
2. **Even perfect container keying cannot split the members.** The
   klist nodes are `device_private` interiors — one origin for all
   devices — and device-class pooling is dominated by born formal
   confluence (the noformal probe) anyway. Container keying alone
   leaves member classes merged: same lesson as origin-split D==1.
3. **Post-chain/post-sysctl, klist welding no longer ranks.** The
   named residual blame at the 223-TU slice: `<synthetic>/join` x20
   (15 subsys) — joins keyed by cells of OPAQUE objects (extern-return
   / summary-minted anonymous objects, unattributable today) — then a
   2-4-subsys tail (`put_cmsg::arg0`, `attribute_container` alloca,
   tcp traceiter args). No klist-family entry above x2. The km-era
   "klist top polluter" reading predates the chain/sysctl levers.

**Consequence: item 2 is re-scoped.** Before any keying build:
(a) opaque-object provenance tagging — record the minting context
(callsite / summary / extern symbol) on opaque nodes so the x20
synthetic bucket gets names (the same move that named the formals);
(b) re-rank; build heap-context cloning for klist ONLY if it
re-appears named. The mechanism sketch above (registrar-anchored
allocation cloning) stays as the design IF warranted.

## Gate ladder

0. THIS CENSUS: ranked weld-cell inventory by welded mass + key-origin
   class. Decision: scope A-list vs generic.
1. Micro: t_chain-style two-instance container test (2 buses, 2
   drivers each; keyed run must resolve 2x2 block-diagonal, pooled run
   4x4) + a mixed-writer demotion test.
2. km fs13: pairs -N/+0 vs current pin, BlobForm INITIAL/giant size,
   fat-tail distribution, wall/RSS budget.
3. 5.18 FI + GT (96->88 FN list must not regress), then kernel fs.
