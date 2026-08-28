# Kernel Precision Killers

What actually destroys indirect-call precision when analyzing the Linux
kernel with a sound, whole-program flows-to analysis — measured, not
guessed. Every killer below carries its mechanism, the kernel idiom that
produces it, the measured evidence, and what recovers it (or doesn't).
Numbers are from the 5.18 / 6.18 campaigns and the 2026-08-23 slice
attribution; repro pointers in the appendix.

Running example: the false pair `__tcp_transmit_skb → ahci_error_handler`.
At the kernel 6.18 fs pin, `__tcp_transmit_skb`'s single icall
(`icsk->icsk_af_ops->queue_xmit`, net/ipv4/tcp_output.c) resolves to
**10,402 targets, 120 of them ata/ahci functions**. The kernel's own
devirt hint at that line (`INDIRECT_CALL_INET`) names the two expected
targets. Everything below is an account of how the other 10,400 got in.

## 0. The frame: the kernel is precise by construction — by keys we discard

The kernel almost never retrieves an object by searching. Every container
is keyed by a **named instance** first and runtime data second:

| container | instance (a named global) | data key (runtime) |
|---|---|---|
| bus device/driver klists | `pci_bus_type`, `platform_bus_type`, … | `match()` over ID tables |
| TCP established hash | `tcp_hashinfo` | netns + 4-tuple |
| UDP hash | `udp_table` | netns + port |
| fd table | per-process `files_struct` | int fd + `f_op == &socket_file_ops` |
| notifier chains | chain-head global | none (call-all) |

and per-object dispatch (`ops` pattern) is bound once at construction
(`icsk->icsk_af_ops = &ipv4_specific` at `tcp_v4_init_sock`) and read
back by field load — the key is object identity, installed where the
constant is still visible.

Two structural facts follow:

1. The instance key is a **constant global exactly one frame above the
   generic layer** (`dev->dev.bus = &pci_bus_type` in the subsystem
   wrapper; the generic `bus_add_device` reads it back from the pooled
   formal). Precision dies one field-read away from a constant.
2. The instance partition tracks subsystem boundaries almost perfectly.
   No kernel lookup keyed for a socket can return an `ata_port`. Every
   cross-subsystem false pair is an artifact of the abstraction, never
   of the kernel's data flow.

## 1. Killer: context-insensitive call junctions (the born giant)

**Mechanism.** Values from every caller meet in a shared function's
formal parameter; assignment (`a`) edges make the union transitive. No
memory, no cells — plain copy-graph confluence.

**Evidence (2026-08-23 slice attribution, 223 TUs spanning net + libata +
driver-core + timers/workqueue/rcu/klist):**
- Before any memory join fires, one assignment-connected component of
  **41,814 value nodes** already contains both worlds: e1000/tg3,
  `skb_segment`, `alloc_workqueue`, `tick_setup_sched_timer`,
  `ata_eh_recover`, `sock_setsockopt`.
- It has **no hub**: largest strongly-connected core = 30 nodes; deleting
  the 24 highest-degree nodes changes nothing (born-hub probe). The glue
  is thousands of small junctions, not a cut vertex.
- **Causal confirmation:** barriering formal arguments in the presolve
  (`--cfl-probe-noformal-presolve`) shatters the largest born class from
  **49,515 to 381** (130x) — subsystem-sized fragments. Note this
  isolates the cause, it is not a fix: the sound solve still propagates
  through calls, and solve-time joins rebuild 41k-55k classes in the
  same run. Removing the glue for real means summarizing or cloning the
  junctions, not skipping them.

**Recovery.** This is the context-sensitivity axis. Per-run summary
adoption (∞-context for provably summarizable functions) removed
167,799 pairs and 17.5% of the born giant at 5.18 FI — and left the
>5000-target caller count flat (353), because the fat sites' delivery
chains (`device_add`-class plumbing) have zero summarizable hops. The
remainder needs cloning/object sensitivity at ~468 dispatch functions,
which is blocked on Killer 2/5 first (see §6 ordering).

## 2. Killer: generic-layer registration formals (container welds)

**Mechanism.** `device_add(dev)` is one function; its `dev` formal is one
node receiving **every device in the kernel**. The insertion
`klist_add_tail(&dev->p->knode_bus, &bus->p->klist_devices)` reads the
bus — the kernel's key — from a field of that pooled formal, so all
buses' containers collapse into one abstract container. Same shape:
`driver_register`, `tracepoint_probe_register`, notifier registration.

**Evidence.** Junction-formal census ranks these formals as the top
union carriers; the km trim census attributes **96.7% of retired-filter
trim to cross-struct hub leakage** (top polluters: `bpf_map_ops`,
tracepoint args, `work_struct`). At 5.18, all fat sites' fptr planes
equal `R[giant]` exactly (183,963) — one pool feeds every fat answer.

**Recovery — the channel recipe (shipped, case studies):** capture the
key at the last frame where it is a constant.
- Tracepoint keyed channels (task #35, default on): per-`__tracepoint_*`
  key; killed the family (zero unclassifiable sites at kernel scale).
- static_call ops tables (task #36, default on).
- Driver-core pilot (bf5ed0d): `CHAINREG(@pci_bus_type, *arg0+32, f1)` on
  the registration wrappers + `CHAINCALL(@pci_bus_type:f0<-arg0)` at
  dispatch. This *is* the kernel's stage-1 key, not an approximation;
  per-bus is the sound ceiling because stage-2 `match()` depends on
  hardware/DT data the corpus cannot see.

## 3. Killer: the registry-probe idiom — `match(dev, drv)`

**Mechanism.** Iterate all candidates in a registry, fire a per-candidate
virtual predicate pairing a container element with a caller-supplied
object: `drv->bus->match(dev, drv)` (`drivers/base/dd.c`); binutils'
`bfd_check_format` over `bfd_target_vector` is the same shape. It smears
**both directions at once**: the fptr is loaded from the pooled element
(`drv->bus` → every bus's match function), and the caller's precise
`dev` is passed into *all* candidates' formals, where `container_of`
casts launder the pool into every subsystem's private types.

**Recovery.** Free once Killer 2 is keyed: the predicate is a virtual
method *of the key instance itself* (`.match` is a constant slot in the
`bus_type` initializer), so instance keying resolves target set,
argument junction, and downstream laundering in one move.

## 4. Killer: per-object ops binding read through a merged pool

**Mechanism.** The `ops` pattern: binding installed at init
(`icsk_af_ops = &ipv4_specific`), retrieved by field load. The kernel's
key is object identity — the one thing a pooled abstraction lacks. Once
the object's class is welded into the giant, the field cell returns
every ops table in the pool, and the arity/type filter keeps whatever
fits (`ahci_error_handler` fits `queue_xmit`'s shape).

**Evidence.** Field sensitivity alone does NOT fix this: the false pair
survives the fs (all+ids) kernel pin. fs splits cells *within* a class;
it does not prevent class merges.

**Recovery.** Not object sensitivity — the field population.
`(struct inet_connection_sock, offsetof(icsk_af_ops))` has ~19 witnessed
install sites; the closed-population intersection is the regfield
channel (`--cfl-regfield-apply`). Caveat measured from source: the
population is not pure rodata — mptcp patches file-static copies, smc
stores a mutable per-socket copy (`&smc->af_ops`) — so the certificate
needs the copy-closure and lands ORANGE, not GREEN.

## 5. Killer: syscall demux and infrastructure-global rendezvous cells

**Mechanism.** A handful of cells where unrelated objects legitimately
co-reside, welding otherwise-separate pools class-by-class.

**Evidence — the measured accretion chain (blob-formation probe, slice):**
the born 49.5k class grows to the 119,609-node final giant through ~56
join events whose keys are *names*:
1. `__se_sys_socketcall::alloca` — `sys_socketcall`'s `unsigned long
   a[6]` demux array, pooling every socket syscall's arguments (the
   first weld event on the socket side);
2. `raw_sendmsg::alloca`, fib globals (`ping_table`, `arp_tbl`);
3. infrastructure globals everything touches: `shadow_timekeeper`,
   `tk_fast_mono`, `tick_cpu_device`, `rcu_state`, `fw_cache`;
4. late events pull in `ahci_post_internal_cmd` et al.

**Recovery.** This is the rendezvous-cell keying target — and the list
is short and concrete. Several entries are cheaper than keying:
timekeeper/tick/rcu state cells carry no fn-ptr-relevant content and are
sink/NOOP-summary candidates; the socketcall demux is a scalar-args
array a summary can prove non-pointer-laundering (long-typed loads).

## 5b. Killer: single-site object caches + singleton containers (the VFS road)

**Mechanism.** VFS inverts the instance-key pattern of §0. Every
`struct file` in the kernel comes from ONE allocation site
(`__alloc_file` → `kmem_cache_zalloc(filp_cachep)`, fs/file_table.c:138),
so under allocation-site heap identity all files — ext4's, sockets',
chardevs', bpf's — are one abstract object before any weld fires. Its
`f_op` cell is a universal rendezvous **by kernel design**:
`sock_alloc_file` stores `socket_file_ops`, `chrdev_open` swaps in each
driver's fops (`replace_fops`), every fs's `do_dentry_open` copies
`inode->i_fop` there. Joining every fops table yields the *sound* wide
answer ("any registered fops"). And the VFS containers are kernel-wide
singletons (`dentry_hashtable`, `inode_hashtable`) whose keys carry
object pointers (parent dentry, sb) — container-instance keying, the
winning lever elsewhere, has nothing to split here.

**Evidence (v2 slice attribution, 317 TUs).** `vfs_read` resolves to 312
targets in-slice (2,761 at the 6.18 pin, 91% inside the one giant core)
including `ata_tdev_match` and `__bpf_prog_run*` — non-fops content, so
the file class itself is welded into the giant. The accretion log names
three roads:
1. **LSM hook formals** — the born component grows 49.5k → 75.2k with
   fs/security TUs added and carries LSM-init members
   (`append_ordered_lsm`); `security_file_alloc(f)` sits inside
   `__alloc_file` itself, handing every file to the hook junctions.
2. **`inode_hashtable` insertion** — repeated join events keyed at
   `__insert_inode_hash`: the global singleton hash chains pool interior
   pointers of every filesystem's inodes (the VFS analogue of the klist
   weld).
3. **The sockfs embedded inode** — join events pairing
   `__sock_create::load` with `__destroy_inode::getelementptr`:
   sockets ARE inodes (`struct socket_alloc`), bridging socket-world to
   inode-world by construction.

**Recovery.** The field-population channel (§4) on
`(struct inode, i_fop)` / `(struct file, f_op)` with 1-2 copy hops
(`do_dentry_open`, `replace_fops`) recovers the sound population and
evicts the non-fops excess; below that population is rarely worth
buying (any fs/chardev genuinely can be behind a generic file). The
dcache's `d_op->d_compare` under `d_same_name` (fs/dcache.c:2251) is a
third sighting of the §3 registry-probe idiom.

## 6. Killers already killed, and the ordering constraint

Three independent falsifications prove precision must be paid in the
abstraction, not at answer extraction:
- **Witness-read** (`--cfl-witness-answers`): sound per-witness answer
  reads equal the pooled answer *exactly* — the content really is in
  the cluster.
- **Origin-split probe**: counterfactual origin-indexed answers remove
  0.000%; cluster diversity D == 1 at all 15,864 sites — object
  indexing is worthless while the welds exist.
- **Adoption vs the tail**: summaries removed 60k+ pairs from fat
  callers, tail flat — only 0.16% of surviving fat-site mass was
  summary-eligible.

Hence the forced order: **fix the spine first** (channels at anchored
idioms — done for tracepoints/static_call, piloted for driver-core;
rendezvous-cell keying for §5), **then** per-object binding (§4) and
cloning (§1 remainder) can pay. Field sensitivity (residue planes) is
orthogonal and already in-graph; flow sensitivity has never been
implicated by any measurement.

## 7. Secondary killers (measured, smaller)

- **Residue collisions (Z_P)**: fs uses offsets mod P (13 default); a
  colliding pair re-welds two fields. Real case: GT recall loss where a
  CPY summary atom relayed residue 0 only and the survivor was the
  offset-104 ≡ 0 (mod 13) accident (fixed 7c152c5, residue-complete
  atoms). `--cfl-field-buckets-auto` picks P against the fn-ptr-slot
  collision census.
- **rodata witness glue**: string literals / const structs as shared
  join witnesses — 47% of km hub joins keyed by one `.str` global.
  Copy-not-unify (`--cfl-rodata-copy`, reviewed model) severs it.
- **Linker-materialized arrays / static_call trampolines**: soundness
  levers, not precision killers, but their absence silently *drops*
  flows — the inverse failure (`--cfl-linker-arrays`,
  `--cfl-static-call`, both default on).

## 8. The thesis: sound, and why generic dials cannot buy the precision back

Decompose the fanout at any fat site into two parts:

1. **The semantic floor** — the feasible population at a genuinely
   polymorphic site ("any registered fops' read" at `vfs_read`). No
   sound analysis can return less. The honest imprecision metric is
   excess *beyond* the population, not raw fanout.
2. **The abstraction excess** — the welds of §§1-5b. For this part,
   each generic sensitivity dial is eliminated by a measurement or a
   structural argument:
   - *Field*: the tcp→ahci pair survives the fs kernel pin — fs splits
     cells within a class, the killers are class merges.
   - *Object/heap*: origin-split D==1, 0.000% excess at all sites; and
     the union legitimately re-forms at retrieval containers (the fd
     table soundly holds every file), so finer upstream identities
     change nothing at the read.
   - *Answer-side*: sound per-witness reads equal the pooled answer
     exactly.
   - *Context (generic k)*: the glue is diffuse (no hub; top-24 degree
     removals flat) and the junctions have thousands of callers, so
     bounded k either misses the junction or multiplies cost without
     separating deep chains; ∞-context summaries — the strongest
     generic contextual weapon — hit a measured 0.16% summarizable-mass
     ceiling at fat sites, blocked semantically (in-body icalls,
     external escapes), not by budget.
   - *Flow*: strong updates require singleton abstract locations; the
     killers are pooled locations by definition. Flow sensitivity's
     benefit is conditional on precision that is already gone.

**Statement — generic containers, semantic keys.** The kernel's
containers are deliberately generic: the same `list_head`/klist/slab
code, offsets, and call shapes for every user — code-reuse genericity
is a kernel design virtue. Consequently every abstraction axis that
partitions by *program structure* (type, field offset, allocation
site, call string, program point) sees identical structure for an ata
port and a socket traversing the same container code, and the quotient
collapses; the five dial failures above are one phenomenon. The
discriminant was never structural — it is a *value*: which instance
the head pointer equals, what the data key hashes to, which constant
was installed. Three corollaries:
1. The semantic key is statically evident at exactly one place — the
   frame where it is still a constant (`dev->dev.bus = &pci_bus_type`
   in the wrapper, `i_fop = &ext4_file_operations` at iget). That is
   the unique frame where syntax and semantics coincide, which is why
   the channel cut goes at the wrapper/install site and nowhere else;
   a channel is the analysis *evaluating the key computation* rather
   than refining a structural partition around it.
2. This is the principled contrast with OO devirtualization: a C++
   vtable is keyed by static type — structural — so class-hierarchy
   analysis works generically. Kernel dispatch keys are runtime values
   (instance pointers, IDs, names); type-based approaches (MLTA-family)
   substitute struct type as a structural surrogate that only partially
   correlates with the semantic key — the source of both their
   imprecision and their unsoundness risk.
3. "Semantic" does not mean dynamic: the keys are static facts — named
   globals, rodata ID tables, closed install populations — recoverable
   by tracking value identities and populations (the certified
   channels), just not by refining structural partitions.
Every lever that moved answers (tracepoint keys, static-call tables,
bus channels, regfield populations) is an instance of reinstating a
semantic key into the abstraction — generic mechanisms, key-guided
instantiation, each machine-certified.

**Scope of the claim:** this is an empirical impossibility argument
with structural explanations, not a theorem over all abstractions.
Unbounded context-sensitive heap cloning separates everything in
principle; the measured structure (diffuse glue, single-site caches
feeding universal containers, unions re-forming at retrieval) is why
every tractable point on that spectrum pays exponentially for zero
excess removed.

## 9. How fat callsites are born: the site-shape taxonomy (2026-08-26/28)

After the certified channels land, a callsite is fat for exactly one
reason: **its dispatch shape carries no key the certifier can
attribute, so it fail-safes into the pooled read**, and its answer is
pool ∩ signature-shape. Direct evidence: the residual per-site pools
are QUANTIZED by call shape — at 5.18 fs the unclamped sites read
4,648 (void(ptr,ptr)) / 4,340 (void(ptr)) / 3,308 (i32(ptr,ptr)) /
2,188 (i32(ptr,ptr,ptr)) targets, the same pool sliced four ways —
and every fat caller is just 2-3 such sites summed. Fatness is a
keyability gap, and keyability is enumerable by IR shape:

| # | site shape (IR) | key carrier | lever / status |
|---|---|---|---|
| 1 | `fn = load(gep S, obj, fieldK)` — typed field GEP | (struct, slot) fn key | regfield-apply, CLOSED-certified (2,303 keys at 5.18) |
| 2 | `fn = load(load(&obj->ops))` — GEP-less SLOT 0 | outer ops-pointer field, object population | regfield-obj; C puts the hot vfunc at slot 0, so this class carried the post-regfield tail (posix_lock_inode proof) |
| 3 | `fn = load(gep(const_tbl, var_idx))` — rodata table, slot-0 element | the const global itself | rodata channels: initializer-bounded, certificate-free (svc_procedure.pc_func, xfrm_dispatch) |
| 4 | `ss->cb[id].call` — var array index INSIDE a loaded pointee | outer field population x stride union | regfield-obj + stride union. LESSON: first cut read element 0 only and dropped TRUE pairs (GT 79->90, nfnetlink/asn1) — caught by the kernel GT bar alone; slice+smoke+per-key ledgers all green |
| 5 | population member is `&table[i]` (interior pointer stored to a field: svc rq_procinfo) | (global, elemOff) members | NAMED, next build: widen objRegs members from GV to (GV, off/var) |
| 6 | dispatch from a typed STACK COPY of the ops fields (dmaengine_desc_get_callback) | the local's key exists; population fails to FLOW (copy-edge witness gap) | named; copyIn witness-class extension |
| 7 | container_of-rooted slot-0 (`notify->notify()` where notify = container_of(work)) | none statically at the site | OPEN: needs container_of-aware site keying (link-inventory applied to dispatch roots) or heap INVOKE pairs |
| 8 | populations with WRITABLE members (i915 display funcs patched at init; mptcp af_ops copies) | refused by certificate | honest residual — may be the true floor for those keys |

Witness-class engineering discipline that produced rows 2-6, worth
stating as method: pick ONE control site (posix_lock_inode), make
every refusal print its excuse (SKIP reason + open@culprit), convert
each named excuse into either a witness class (same-typed bulk copies;
untyped same-offset copies; container_of-anchored copies via a
per-struct link-member inventory; Gobjs canonicalization of extern
population decls; memcpy-escape declassification) or an honest
refusal. Every class lands with its own audit tag; the total stated-
assumption surface after all of it is TWO tagged keys kernel-wide.

Campaign effect on the tail (5.18 fs, callers >= 5,000 targets):
337 (pre-regfield) -> 92 (fn tables) -> 90 (+obj) -> 85 (+witness
trio); pairs 15.1M -> 6.09M with GT FN-identity (79) held at every
gate. The rodata/stride pair (rows 3-4) gates at FI (-6,977/+0);
remaining tail mass = rows 5-8.

## Appendix: repro

- Slice corpus: `/data/csong/tmp/bclist-skweld` (223 TUs of 5.18:
  net/core, net/ipv4, drivers/base, drivers/ata, kernel/time,
  workqueue, rcu, klist/kobject, loopback, ethernet). The false pair
  reproduces fully in it (1,207 targets incl. `ahci_error_handler`);
  adding bpf/trace/events/VFS/security (v2, 317 TUs) only widens the
  pool to 1,799 — riders, not causes.
- Runs (logs in `/data/csong/tmp/`): `skweld3.log` (fixed coupler census,
  14 subsystems + blob formation + `--cfl-trace-fptr`), `skweld-hub.log`
  (born-hub shatter), `skweld-noformal.log` (formal-barrier presolve).
- Flags: `--cfl-flows-to --cfl-nexus-fields=all+ids
  --func-summaries=func_summaries.txt` plus per-run probe flags; see
  docs/cli-reference.md §Probes.
- Kernel-scale pins: 6.18 fs all+ids (16,472 icalls / 13.1M pairs),
  5.18 FI adoption gates (−167,799/+167, GT 96 FN-list identical).
- Instrument caveat recorded the hard way: slice ICALL dump targets are
  after `" -> "`, not field 3; and the coupler census needs the
  corpus-root fix (a3e579e) on absolute-path bc-lists.
