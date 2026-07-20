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
