# LangRef coverage map — what the encoder covers, what our corpora test

Date: 2026-07-22. Companion to `docs/kernel-census/`. Answers a
different question than the census: the census audits *observed*
constructs; this map audits the disposition table against the **full
LLVM language** (LangRef), so we know what a NEW corpus could bring
before it arrives.

Enforcement layers:
1. `opcodeTableGaps()` — mechanical check of the disposition table
   against `llvm/IR/Instruction.def`: **every opcode LLVM defines has
   a disposition** (corpus-independent; verified in every census run
   and counted as UNDISP by `--ir-census-strict` if a future LLVM adds
   opcodes).
2. Intrinsic families from LangRef that our corpora have NEVER
   produced are pre-dispositioned (mostly SUSPECT = encoder work
   required); unknown names still land on UNDISP + strict abort.
3. Operand bundles (a LangRef feature orthogonal to opcodes) are now
   tallied per tag.

## Instructions — TOTAL (68/68 opcodes dispositioned)

| group | disposition | tested by our corpora? |
|---|---|---|
| memory/data core (load, store, gep, phi, select, casts, binops, …) | HANDLED | yes — all corpora, pinned baselines |
| calls (call, invoke, callbr) | HANDLED | call: everywhere; invoke: libpng harness; callbr: kernel asm-goto |
| IR-level atomics (atomicrmw, cmpxchg) | HANDLED | t_atomicptr only — kernel has ZERO (x86 atomics are asm) |
| int-provenance casts (trunc/zext/sext) | SUSPECT, witness-covered | t_atomicptr, t_linkerarray; NOTE census ptr-relevance can't see laundered ints — witness LEDGER is the real meter |
| **C++ EH (landingpad, resume)** | **SUSPECT — unmodeled** | **barely: 11 instances in libpng's fuzzer harness. harfbuzz is `-fno-exceptions`. Thrown-object flow (`__cxa_throw` → landingpad) has NEVER been validated** |
| windows EH (catchpad/cleanuppad/catchswitch/…) | NOOP (absent) | never |
| indirectbr | NOOP (control) | blockaddress dispatch untested |
| freeze, addrspacecast | HANDLED | census-era fixes |
| vaarg | HANDLED | vararg wiring tested |
| UserOp1/2 | NOOP (pass-internal, never serialized) | n/a |

## Intrinsic families — observed vs pre-dispositioned

Observed and dispositioned (kernel/libpng/harfbuzz/php/musl): memcpy/
memmove/memset (HANDLED), dbg/lifetime/assume/expect/overflow/bit/fp
families (NOOP), va_copy (SUSPECT, 10 kernel instances), masked
vector ops (SUSPECT, 0 in kernel), x86 target intrinsics (SUSPECT).

Never observed, now pre-dispositioned so first contact yields a
verdict (all SUSPECT unless noted — SUSPECT = do NOT trust results on
a corpus using these until the encoder models them):

| family | why it matters for a callgraph |
|---|---|
| `llvm.coro.*` (C++20 coroutines) | frame pointer laundering through opaque frame |
| `llvm.experimental.gc.*`, gcroot/read/write | statepoints RELOCATE pointers |
| **`llvm.type.checked.load`** | **returns a function pointer from a vtable — CFI/whole-program-devirt C++ (Android/Chrome)** |
| **`llvm.load.relative`** | **relative-vtable read — the intrinsic form of `offset_to_ptr`; wire like the inttoptr pull rule** |
| **`llvm.icall.branch.funnel`** | **CFI fptr dispatch funnel** |
| `llvm.threadlocal.address` | LLVM 16+ TLS lowering — should alias its operand |
| `llvm.vp.*` (vector predication) | predicated loads/stores/gathers |
| `llvm.ptrauth.*` (arm64e) | signs/strips pointers |
| `llvm.wasm.*`, `llvm.seh.*`, `llvm.eh.*` | EH state machinery |
| `llvm.localescape/localrecover` | frame-slot address capture (SEH) |
| `llvm.ssa.copy`, deoptimize/guard | value copies / deopt state |
| aarch64/arm/riscv/amdgcn/nvvm targets | per-name review like x86 |

## Module-level features

| feature | status |
|---|---|
| llvm.global_ctors/dtors | handled (CallGraph.cc:5585) |
| ifunc resolvers | handled (collectIFuncTargets) — kernel has 0; userspace ifuncs untested beyond unit level |
| aliases | canonicalized |
| module-level inline asm | census'd + linker-array model (task #22) |
| section-attributed globals + `__start_/__stop_` bounds | modeled (task #22), universal LEDGER |
| operand bundles (deopt, funclet, kcfi, ptrauth, …) | counted per tag by census; funclet/deopt semantics unmodeled (matter only with EH/managed corpora) |
| blockaddress / prefix / prologue data | not modeled; indirectbr is control-only |
| comdat, linkage, visibility | handled by GUID linking |

## The honest "untested language features" list

Ordered by likelihood we ever meet them:

1. **C++ exceptions with pointer payloads** — closest gap; any
   exception-built C++ corpus needs `__cxa_throw`/landingpad modeling
   first. (Current exposure: 11 LEDGERed instances, libpng harness.)
2. **CFI / relative-vtable C++** (`type.checked.load`,
   `load.relative`, branch funnels) — required for Android/Chrome-
   style corpora; directly callgraph-relevant.
3. C++20 coroutines.
4. Scalable/predicated vectors (SVE/RVV codegen).
5. GC statepoints (managed-language frontends).
6. Windows EH, ptrauth, wasm.

Everything above fails LOUD, not silent: unlisted names → UNDISP →
`--ir-census-strict` abort; listed-but-SUSPECT → counted instances in
the census summary and JSON ledger.
