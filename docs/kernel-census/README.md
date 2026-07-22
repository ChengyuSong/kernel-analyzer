# Linux 6.8.2 IR-construct census — the kernel's residual unsoundness surface

Date: 2026-07-20. Tool: `KAMain --ir-census --ir-census-strict
--ir-census-out=...` (commit 0cf2783), run over the full kernel bclist
from `~/fast/linux/linux-6.8.2`.

Artifacts in this directory:
- `linux-6.8.2-ir-census.json.gz` — the machine-readable ledger
  artifact: every opcode/intrinsic disposition with instance counts,
  all 1,136 external callees, constexpr tallies, the full classified
  inline-asm table (4,921 distinct templates), and the `ledger` array
  (every construct class the encoder does not model, with counts).
  Read with `zcat`.
- `census-run.log` — the human-readable CENSUS lines from the same run.

## Corpus

57,661 defined functions, 4,802,515 instructions, 129,812 inline-asm
call sites (4,921 distinct `(constraint-string, asm-text)` templates),
1,136 external declarations without definitions.

## Closed world holds

**0 undispositioned construct kinds.** Every opcode and intrinsic in
the corpus has an explicit HANDLED / NOOP / SUSPECT entry in the
disposition table, so `--ir-census-strict` passes — and is now cheap
enough (~30 s over module loading) to run as a permanent gate: a future
kernel/compiler that introduces a construct the edge builder has no
disposition for kills the run instead of silently dropping edges
(the default InstVisitor handler is a silent no-op; this gate is the
mechanical negation of that failure mode).

Remaining SUSPECT ptr-relevant instances: **16** in 4.8M instructions —
`llvm.va_copy` (10) and `llvm.experimental.noalias.scope.decl` (6,
metadata-only in practice, ledgered conservatively).

## Inline asm, classified: 13.7% of sites can move a pointer

The prior census pinned inline asm as the dominant untyped exposure:
129,812 sites. That number treated every asm site as an unknown.
Classifying each site by its constraint signature — output types,
indirect (`*m`) operands and their mandatory `elementtype` widths,
register vs immediate pointer arguments, memory clobbers — splits the
exposure by what the asm is *physically able* to do to value flow:

| category | sites | distinct | meaning |
|---|---:|---:|---|
| ptr-out | 1,244 | 27 | result carries a pointer — asm can mint one |
| mem-ptr | 498 | 8 | indirect operand typed as pointer — loads/stores pointer values |
| ptr-in-reg | 4,893 | 35 | raw pointer escapes into asm by register |
| mem-ptr-width | 11,169 | 101 | indirect operand of i64/i128 width — could launder a pointer |
| **exposed subtotal** | **17,804 (13.7%)** | **171** | **ptr-capable — on the ledger** |
| mem-narrow | 25,973 | 119 | accessed slots narrower than a pointer — physically cannot |
| imm-ptr | 23,132 | 5 | pointer bound to an immediate constraint, no memory clobber: link-time symbols embedded in `__bug_table` / `__jump_table` metadata sections, no runtime flow |
| barrier | 57,955 | 4,594 | memory clobber / side effect only, no ptr-capable operands (the 4,594 distinct are one-off ALTERNATIVE/exception-table expansions with inlined labels) |
| pure | 4,948 | 32 | int/flag computation, no memory |

The rule making imm-ptr sound: an immediate-pointer template that
*also* clobbers memory classifies as ptr-in-reg (it could store the
symbol somewhere the program reads).

So the true modeling surface is **171 distinct templates**, not 4,900,
and 86.3% of all asm sites are *provably irrelevant to pointer flow*
from their signatures alone.

## The 171 exposed templates, by family

| family | sites | distinct | assessment |
|---|---:|---:|---|
| bitops (`btq/btsq/btrq/btcq`) | 7,336 | 10 | operate on `unsigned long` bitmap words — width-capable, semantically bit flags; candidates for justified NOOP-by-family |
| percpu (`%gs:`) | 5,918 | 11 | `this_cpu_read/write`, `current` — **real pointer flow**, mechanically modelable: the percpu variable is the operand, elementtype gives the width |
| atomic RMW (`lock`/`xchg`/`cmpxchg`/`xadd`) | 1,310 | 18 | pointer-slot exchanges (`xchgq`, `lock cmpxchgq`) — **real pointer flow**, same fused store+load shape as `visitAtomicRMWInst` |
| misc arithmetic on i64 slots (`addq/incq/movq $1,$0`) | 832 | 81 | atomic64/counter templates; mostly counters, a few `movq` moves are genuine |
| flags save (`pushf; pop`) | 777 | 2 | RFLAGS in an i64 — never a pointer; justified NOOP |
| uaccess stubs (`call __get_user_*` / `__put_user_*`) | 753 | 4 | user↔kernel copies; kernel fptrs must never round-trip via user memory (assumption, recorded) |
| uaccess inline (`__ex_table` fixup mov) | 396 | 29 | same assumption |
| ALTERNATIVE + call (paravirt/retpoline) | 293 | 6 | **indirect calls hidden in asm** — direct callgraph exposure, same family as static_call (task #14) |
| string ops (`rep movs/stos`) | 48 | 3 | memcpy/memset-shaped; modelable like `llvm.memcpy` |
| other calls / empty templates | 148 | 7 | reviewed individually in the JSON |

Actionable ranking for the encoder (highest pointer-flow value per
template first):

1. **percpu `%gs` pointer ops** — 11 templates cover 5,918 sites; the
   `mem-ptr` subset (498 sites) is typed pointer load/store of percpu
   slots (`current` etc.) and is a straight d-edge encoding.
2. **atomic pointer xchg/cmpxchg in asm** — the ptr-out `xchgq`/`lock
   cmpxchgq` templates (~600 sites); the IR-level equivalents are
   already handled, these are the same semantics behind a template.
3. **ALTERNATIVE call templates** — 293 sites of asm-wrapped indirect
   calls; fold into the static_call/paravirt work (task #14).
4. Everything else is either justified-NOOP-by-family (bitops, flags)
   or covered by a stated assumption (uaccess).

## Module-level: linker-mediated pointer flows (2026-07-20, second pass)

The instruction-level census above is structurally blind to a second
exposure: pointer bindings assembled by the LINKER, not by IR
instructions. On x86-64 (PREL32 relocations), `__initcall(fn)` emits
**module-level** inline asm (`.section .initcallN.init` + `.long fn -
.`); consumption reads linker-defined `__start_X`/`__stop_X` extern
globals that have no definition in any TU — so today a flows-to load
from them yields ∅ and e.g. `do_one_initcall`'s indirect call resolves
to nothing. The census now walks `getModuleInlineAsm()`, sectioned
globals, and undefined extern globals (`module_level` object in the
JSON artifact).

Kernel numbers:
- **module asm**: 1,494 modules carry blobs; 27 distinct target
  sections; 3,490 symbol entries. By family: pci_fixup_\* 1,671,
  __tracepoints_ptrs 964, .initcall\*.init 646, __ex_table 32.
- **sectioned globals** (regular IR globals the encoder already sees;
  only the linker-array *read* is unconnected): __param 534,
  __tracepoints 964, __bpf_raw_tp_map 964, _ftrace_events 1,828,
  .init.setup 314, _ftrace_eval_map 549, .x86_cpu_dev.init 5,
  .apicdrivers 1.
- **undefined extern globals**: 199, of which **106 are linker-array
  bounds** (`__start_/__stop_/..._start/_end`) — with real IR loads:
  `__start___param` (5 uses), `__start_builtin_fw` (6),
  `__stop___jump_table` (6), `__start_static_call_sites` (4), …
- **`.discard.addressable` stubs**: 16,915 stubs naming **12,597
  distinct functions** (21.8% of all 57,661) — the IR-visible catalog
  of everything referenced from asm/linker plumbing, and the key that
  makes the model below possible without parsing asm text.

### vmlinux cross-reference: what the linked image says the arrays hold

Sampling each bounds-delimited array in the built vmlinux (content
classified as ABS64 kernel VAs vs PREL32 offsets vs data):

| array | bytes | content | fptr-relevant? |
|---|---:|---|---|
| initcall0–7/rootfs | 2,449 | PREL32 fn offsets | **yes — do_one_initcall** |
| setup (`.init.setup`) | 7,536 | ABS64 (obs_kernel_param.setup_func) | **yes — obsolete_checksetup** |
| __param | 21,520 | ABS64 (kernel_param → ops->set/get) | **yes** |
| pci_fixup_\* | ~14,800 | PREL32 fn offsets (quirk hooks) | **yes — pci_do_fixups** |
| ftrace_events | 14,888 | ABS64 (trace_event_call → class ops) | **yes** |
| _bpf_raw_tp | 31,904 | ABS64 (bpf_raw_event_map.bpf_func) | **yes** |
| __tracepoints_ptrs | 3,988 | PREL32 → tracepoint structs | partial — probe funcs register via IR-visible calls |
| static_call_sites | 105,032 | PREL32 call-site addrs | task #14 (patching, not data flow) |
| mcount_loc | 396,920 | ABS64 code addrs | no — ftrace patch points, control only |
| __ksymtab/_gpl | 142,956 | PREL32 export offsets | only for out-of-tree module loading |
| orc_\*, __bug_table, __ex_table, __jump_table | ~5.8 MB | PREL32 metadata | no — unwind/traps/patching |

So the fptr-relevant linker arrays are: **initcalls, setup, __param,
pci_fixup, ftrace_events, bpf_raw_tp** (≈6,100 pointer entries total),
plus the tracepoint iteration side. Everything larger is unwind/patch
metadata with no pointer-value flow.

### The model (phase B, task #22)

Section-array unification: for each `__start_X`/`__stop_X` (and
initcall/setup families), alias the extern bounds symbol to a
synthetic array node into which every section-X global flows; module-
asm PREL32 entries contribute their target functions (recoverable via
`.discard.addressable` stubs — no asm-text parsing needed). One
mechanism covers all six families. Differential test:
`do_one_initcall`'s V-set goes from ∅ to the ~646 initstubs.

**Shipped 2026-07-22 (commit 4907f3b), with two corrections the
implementation forced:** (1) wired bounds symbols need their OWN node
identity — `getValueNodeFor` returns the universal unknown-memory node
for every undefined extern, and wiring members into it leaked them to
every unmodeled-extern read in the kernel (+2.7M pairs before the
fix); (2) in-place (ABS64) and encoded (PREL32) members need different
edges — value aliasing vs deref + a gated `offset_to_ptr` pull.
Result: `do_one_initcall` 85 → 735 targets (649 initstubs), whole
kernel pinned at 14,850 icalls / 5,866,561 pairs (superset, +26
icalls). static_call/ksymtab families stay excluded + LEDGERed.

## The full residual ledger (per-corpus unsoundness bill)

From this census plus the 2026-07-20 whole-kernel solve run:

| entry | instances | status |
|---|---:|---|
| asm ptr-capable sites | 17,804 (171 templates) | classified above; top 3 families modelable |
| interprocedural int provenance (solve-time LEDGER) | 22,794 declined accesses | witness depth-8 declines; next lever after asm |
| external boundary | 1,136 declarations | top mass = `__SCT__*` static_call trampolines (task #14) |
| SUSPECT intrinsics | 16 instances | va_copy, noalias.scope.decl |
| landingpad/resume | 0 in kernel | C++ corpora only |

Every entry is loud (LEDGER counters or this artifact), none is a
silent drop — the census's no-silent-fallback contract, now enforced
by `--ir-census-strict`.
