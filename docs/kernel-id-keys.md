# Kernel ID / Match-Key Study

Companion to docs/kernel-precision-killers.md §8 ("generic containers,
semantic keys"): a survey of the semantic keys the kernel actually
matches on — where they are documented (ref, don't re-derive), their
in-tree populations, and which are statically recoverable for
channel/population modeling. Source censuses at v5.18
(/data/csong/opensource/linux-stable).

## 1. The kernel's own registries (documented — cite these)

The ID namespaces are NOT folklore; the kernel centralizes them:

- **`include/linux/mod_devicetable.h`** — the canonical registry of
  match-ID types: **55 `*_device_id` struct definitions** at v5.18
  (pci, usb, hid, acpi, of, i2c, spi, platform, virtio, vmbus, x86cpu,
  …). Every bus's `match()` compares against one or more of these.
- **`scripts/mod/file2alias.c` `devtable[]`** — machine-readable list of
  **49 modalias namespaces** (+ usb, special-cased): each entry names
  the namespace prefix and the encoder that turns an ID-table entry
  into the `MODULE_ALIAS` string udev matches at hotplug. This file IS
  the kernel's own statement of "these are my match-key namespaces."
- **`Documentation/driver-api/driver-model/`** (bus.rst) — the
  `bus->match(dev, drv)` contract.
- **`Documentation/admin-guide/devices.txt`** — the LANANA registry of
  static char/block `dev_t` major/minor assignments.
- **`Documentation/devicetree/bindings/`** — YAML schemas for OF
  `compatible` strings; the largest namespace by far.
- External (out-of-tree) authorities: PCI-SIG vendor/device IDs
  (pci.ids), USB-IF VID/PID (usb.ids), ACPI HIDs (ACPI spec + UEFI
  registry), IANA for the network numbers (AF_*/IPPROTO_*/ETH_P_* uapi
  constants mirror it).

## 2. Bus-side census (ours)

**109 `struct bus_type` instances with `.match`** at v5.18 (full list:
/data/csong/tmp/bus-match-census.txt; extraction one-liner in git log).
Match implementations fall into five key kinds:

| key kind | example buses | driver-side key | device-side key |
|---|---|---|---|
| rodata ID-table walk | pci, usb, i2c, spi, sdio, hid, virtio | `*_device_id[]` const array | hardware registers (vendor/device, VID/PID) |
| firmware namespace | OF `compatible`, ACPI `_HID` (via of/acpi helpers in many matchers) | const strings in driver | DT/ACPI tables at boot |
| name strcmp | platform (fallback), auxiliary (`modname.id`), apr | const `.name` | often ALSO a build-time const (static devices, mfd cells) |
| CPU feature bits | cpu, x86cpu | `x86_cpu_id`/`cpu_feature` | CPUID at boot |
| match-all / trivial | some virtual buses (probe decides) | — | — |

`platform_match` (drivers/base/platform.c:1347) is the canonical
layered fallback: `driver_override` string → OF → ACPI → `id_table` →
name equality. `pci_bus_match` → `pci_match_device` over `id_table`
(+ dynamic ids added via sysfs `new_id` — a mutable exception worth
remembering).

## 3. Population census (sizes the per-namespace channel value)

`MODULE_DEVICE_TABLE(<ns>, …)` counts kernel-wide at v5.18 — i.e., how
many driver ID tables exist per namespace:

    of 3645 | i2c 1035 | pci 833 | acpi 430 | usb 355 | spi 246
    platform 206 | hid 119 | pcmcia 49 | mdio 46 | x86cpu 45
    serio 39 | dmi 33 | amba 33 | pnp 29 | virtio 24 | auxiliary 20 …

For an x86_64 server corpus the relevant head is pci, acpi, i2c, usb,
platform, hid, virtio, vmbus, auxiliary, mdio, serio — the mechanical
CHAINREG worklist, in roughly that order.

## 4. Beyond the driver model: the other key namespaces

From the container studies (sockets, VFS, driver core):

- **`dev_t`** — `kobj_map` (cdev_map/bdev_map) keyed (major,minor);
  static majors documented in devices.txt; dynamic majors/misc minors
  are runtime-allocated.
- **Network numbers** — `AF_*` (socket family array), `IPPROTO_*`
  (`inet_protos[]` — note: *array-index dispatch*, statically
  resolvable when the index is constant), `ETH_P_*` (ptype hash),
  netlink protocol numbers; genetlink families match by NAME string.
- **Filesystem names** — `file_system_type.name`, string-keyed
  registry at mount (`get_fs_type`).
- **Tracepoint / static_call identities** — per-key named globals; our
  #35/#36 channels already consume these.
- **Runtime-only handles (NOT statically recoverable)** — idr/xarray
  ids (fds, bpf prog/map ids, loop minors), ephemeral ports, dynamic
  majors: for these the container *instance* is the static ceiling.

## 5. Classification for the analysis

What matters for channels is whether the key is a static fact:

1. **Both-sides-static** (strongest: closed pair population):
   name-matched platform/auxiliary devices declared in-tree, static
   majors, constant-index array dispatch, tracepoint/static_call keys.
   These support full pair certification (regfield/CHAINREG GREEN).
2. **Driver-side-static, device-side-hardware** (pci/usb/i2c/…):
   the ID tables are rodata but the device's identity arrives from
   hardware/firmware at runtime. Sound ceiling = **per-bus instance**
   (the CHAINREG pilot); finer needs a closed-world certificate that
   is false by construction for hotpluggable buses. The `new_id` sysfs
   backdoor makes even the driver-side table technically mutable —
   channels must treat it as population-extending, not violate
   soundness silently.
3. **Runtime handles**: instance-level keying only.

Corollary (matches killers-doc §3): wherever the match predicate is a
virtual method *of the key instance* (`bus->match`, `d_op->d_compare`),
instance keying resolves the predicate icall itself for free — the
fptr and the population share the key.

## 6. What this study changes

- The CHAINREG extension is a **worklist with documented semantics**,
  not reverse engineering: each bus's key kind and ID namespace is in
  mod_devicetable.h/file2alias.c, so writing the wrapper summaries is
  transcription plus offset lookup.
- Namespace populations (§3) rank the buses by expected answer mass.
- The both-sides-static class (§5.1) is an untapped tier: platform
  devices declared with constant names could support *within-bus* pair
  narrowing under a closed-population certificate — unlike pci/usb
  where per-bus is provably the ceiling.
- Anything we model here can cite the kernel's own registry rather
  than asserting idiom knowledge — relevant for the paper's
  "domain-informed but not folklore" positioning.

## 7. Consumption design: grammar as the only interface

The solver core stays generic — it knows planes, joins, and keyed
channel cells; CHAINREG/CHAINCALL atoms are the sole channel
interface. The registry is consumed by a producer of atoms, not by
solver code:

- **Not hand-transcription at scale.** Byte offsets are layout- and
  version-specific (the same reason adopted atoms never enter the
  shared func_summaries.txt); 109 hand-maintained bus entries would be
  exactly the hardcoded-idiom-knowledge criticism §6 positions against.
- **A per-run chain prover** (`--cfl-propose-chain-summaries`, regfield
  discipline): detect wrappers by the thesis rule — the key is
  constant at exactly one frame. REG side: store of a bus_type
  global's address into a formal-reachable field + registration-call
  reachability → CHAINREG for every fn-ptr slot of the formal's struct
  (StructAnalyzer offsets: layout-correct by construction; all-slots =
  sound superset, zero per-bus knowledge). CALL side: constant .bus
  store reaching device_add → CHAINCALL. Certificate: every store to
  the .bus field along the path is the constant, else refuse LOUDLY.
  new_id-style dynamic tables are population-extending, never closing.
- **Conservative binding policy**: fN formal binding is per-bus
  semantics and a wrong bind is unsound; default f9 (no bind) unless
  the wrapper body proves the correspondence — answer-side resolution
  is where the win is.
- **Two grammar generalizations only**: literal channel keys
  ((namespace, string|const-index) for the §5.1 both-sides-static tier
  and exact array-index dispatch), and a wildcard slot form
  (*arg0+@X).
- **Sequencing**: mechanical top-population buses as gated pilot lines
  now → chain prover, gated by re-deriving the pilot lines
  byte-for-byte on 5.18 → retire hand lines → literal-key tier last
  (only step touching solver-side key plumbing). #35/#36 stay bespoke
  (shipped, gated); re-expression as atoms is optional hygiene.
