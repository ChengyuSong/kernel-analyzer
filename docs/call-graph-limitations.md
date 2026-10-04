# Call Graph Construction Limitations

This document records known limitations and gaps in the current call graph
construction (`CallGraphPass` in `src/lib/CallGraph.cc`).

## 1. `@llvm.global_ctors` / `@llvm.global_dtors`

**Status**: Handled.

`processCtorsDtors` (`CallGraph.cc`) parses the `@llvm.global_ctors` and
`@llvm.global_dtors` arrays in each module and records listed functions in
`Ctx->CtorDtorFuncs`. This set is available as implicit entry points for
downstream analyses (e.g., reachability). No CFL edges are created since
these are implicit calls with no arguments or return values used by LLVM IR
code.

## 2. `GlobalIFunc` (GNU indirect functions)

**Status**: Handled.

`collectIFuncTargets` (`CallGraph.cc`) analyzes each ifunc's resolver
function to collect all possible target functions. It handles both direct
`ret @func` patterns and the common `store @func, %alloca` /
`load %alloca` / `ret` pattern used by unoptimized resolver builds. Call
sites targeting an ifunc symbol are resolved in `visitCallBase` to the
concrete targets instead of falling through to `IndirectCallInsts`.

**Remaining limitation**: Resolver functions with more complex control flow
(e.g., returning values from nested calls or global lookups) are not
analyzed beyond the store-to-alloca pattern.

## 3. `hasAddressTaken()` limitations

**Status**: Known but acceptable for CFL-based approach.

`F.hasAddressTaken()` (`CallGraph.cc:932`) is used to populate
`AddressTakenFuncs`, which serves as the candidate set for type-based
fallback matching (`findCalleesByType`). This API has several edge cases:

- **False positives**: Functions in `@llvm.global_ctors` have their address
  taken (stored in a global array) but are not realistic indirect call targets.
  Currently mitigated by `isCompilerIntroducedValue` skipping those globals.
- **False negatives with `ifunc`**: The actual implementation function
  (returned by the resolver at runtime) may not have its address taken in
  LLVM IR. `hasAddressTaken()` returns `false` for it.
- **False negatives with `@llvm.used`**: Functions in `@llvm.used` are
  skipped by `isCompilerIntroducedValue`. If a function appears only in
  `@llvm.used` (e.g., referenced from inline asm or linker scripts), it
  won't be in `AddressTakenFuncs`.

The CFL points-to analysis largely supersedes `hasAddressTaken()` for
indirect call resolution, so these gaps mainly affect the type-based fallback.

## 4. Inline assembly

**Status**: Handled (`handleInlineAsm`, `GraphBuild.cc`), with stated
over-approximations.

- **Operands.** Tied outputs become copy edges. Indirect memory operands
  (`=*m`, `*m`) on pointer or pointer-width integer slots become a store
  to or a load from the slot's cell; this covers `this_cpu_read/write`
  and `xchg`/`cmpxchg` on `i64`. Raw `"p"`/`"r"` pointer inputs flow into
  the result, and, when the asm has a `"memory"` clobber or an indirect
  output, also into every written cell. `"i"` immediates are skipped
  unless the text reads `%gs:`/`%fs:` (the `current` idiom).
- **Calls inside the asm text.** `call foo` is resolved by name
  (`handleCall`), trying the size-suffixed variants of `__put_user_${N}`
  style placeholders.
- **Addresses taken in module-level asm.** Entries such as
  `.long fn - .` in linker-gathered sections (initcalls, `pci_fixup`,
  tracepoint pointers) mark `fn` as address-taken and make it a member of
  the section array read through `__start_X`/`__stop_X`
  (`--cfl-linker-arrays`, `wireLinkerSectionArrays`). Members of
  sections with incomplete membership keep the universal node and are
  ledgered; excluded families (ksymtab/kcrctab, static_call, jump_table,
  ex_table, orc, mcount, ...) are ledgered in `CallGraph.cc`.

**Remaining limitations**: asm effects are summarized from constraints,
not from the instruction text; an indirect call written in the asm text
(`call *%reg`) is not resolved, and a direct `call` the name match cannot
resolve is missed; per-cpu `inttoptr(ptrtoint @pcpu + off)` rebasing is modeled
only for globals in a `percpu` section (other rebasing is a counted
residual).

## 5. `inttoptr` / integer-cast function pointers

**Status**: Handled, with provenance witnesses.

`visitPtrToIntInst` and `visitIntToPtrInst` add assignment edges through
the integer. `visitBinaryOperator` adds an edge from EVERY
pointer-derived operand to the result, so `ptr - ptr`, `ptr + var` and
the kernel's `offset_to_ptr` / PREL32 consumer
(`add(ptrtoint base, sext(*entry))`) all carry the pointer.
Pointer-width integer loads, stores, phis, selects, returns, arguments
and varargs are wired when a provenance witness (`mayCarryPtrProvenance`
/ `mayBecomePointer`, depth 8) says the integer may hold a pointer.
In field-sensitive mode a `ptrtoint` adds a wildcard (unknown offset) on
its source unless every use is a tag round trip (low-bit or/xor/and,
compare, `inttoptr`; `ptrToIntTagRoundTripOnly`); reasons are tallied in
the wildcard census.

**Remaining limitation**: the witnesses are syntactic and bounded
(depth 8); an integer that carries a pointer past that depth, or through
a path they do not follow, loses the flow.

## 6. `va_arg` extraction

**Status**: Handled.

The call handling code (`handleCall`, `CallGraph.cc:334-351`) connects actual
arguments at call sites to the function's vararg node. `visitVAArgInst`
creates assignment edges from the function's vararg node to the `va_arg`
result node when the result type is a pointer, completing the dataflow
from caller arguments through the vararg aggregate to the extracted value.

## 7. `blockaddress` / computed goto

**Status**: Not applicable to call graph, noted for completeness.

`indirectbr` instructions using `blockaddress` constants implement computed
gotos (GCC extension). These do not create inter-procedural call edges but
affect intra-procedural CFG completeness. Used in the kernel's threaded
interpreter and some generated code.
