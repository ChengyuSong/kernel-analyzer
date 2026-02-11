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

**Status**: Not handled (known issue, to be addressed separately).

`visitCallBase` (`CallGraph.cc:490`) skips inline assembly calls entirely.
This causes two categories of missing edges:

- **Calls inside inline asm**: Functions called from inline assembly blocks
  are invisible to LLVM's use-def chains.
- **Address-taken via inline asm**: The Linux kernel extensively uses inline
  asm to place function pointers into special sections (e.g., `__initcall`,
  syscall tables, exception tables). These references are not visible as
  LLVM IR uses of the function, so `hasAddressTaken()` returns `false` and
  the CFL graph has no edges for them.

## 5. `inttoptr` / integer-cast function pointers

**Status**: Not handled.

`visitIntToPtrInst` (`CallGraph.cc:765`) only logs a warning; no CFL edges
are created. If a function pointer is cast to an integer and later cast back
via `inttoptr`, the points-to information is lost. This pattern appears in
some kernel code paths.

**Fix**: Difficult to handle soundly. Options:
- Track `ptrtoint`/`inttoptr` pairs and create assignment edges between them.
- Conservatively treat `inttoptr` results as potentially pointing to any
  address-taken function (expensive).

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
