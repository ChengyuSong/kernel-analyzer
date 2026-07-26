# libpng FieldFilter Debug Notes (2026-02-27)

## Context

Observed behavior while analyzing:

`test/libpng/libpng_read_fuzzer.0.0.preopt.bc`

At indirect call in `png_do_read_transformations`, only
`png_read_filter_row_sub` was rejected by `FieldFilter`, while
`png_read_filter_row_up/avg/paeth_*` were kept.

Example log pattern:

```text
CallGraph: Handle indirect CallSite: call void %498(...)
CallGraph:   fptr node 5425 V-set size: 8951
CallGraph: Handle indirect target: png_read_filter_row_avg
CallGraph: Handle indirect target: png_read_filter_row_paeth_1byte_pixel
CallGraph: Handle indirect target: png_read_filter_row_paeth_multibyte_pixel
CallGraph: FieldFilter: reject png_read_filter_row_sub for struct.png_struct_def field 9
CallGraph: Handle indirect target: png_read_filter_row_up
```

## Repro command

```bash
./debug/lib/KAMain test/libpng/libpng_read_fuzzer.0.0.preopt.bc --verbose 3
```

Useful grep:

```bash
rg -n "FieldFilter: reject png_read_filter_row_|Handle indirect target: png_read_filter_row_" /tmp/ka_libpng_verbose3.log
```

## IR ground truth

In `png_init_filter_functions`, all five function pointers are stored into the
same table field (`%struct.png_struct_def` field 118, array slots 0..3):

- `@png_read_filter_row_sub`
- `@png_read_filter_row_up`
- `@png_read_filter_row_avg`
- `@png_read_filter_row_paeth_1byte_pixel`
- `@png_read_filter_row_paeth_multibyte_pixel`

So asymmetric evidence is suspicious.

## A/B check against extern-decl canonicalization patch

Question: Did commit `f64a748` (extern declaration identity canonicalization)
cause this?

Result: No.

Method:
- Temporarily restored `src/lib/NodeFactory.{h,cc}` to `116ee78`
- Rebuilt and reran the same libpng command
- Same outcome: only `png_read_filter_row_sub` rejected
- Restored current `NodeFactory` and rebuilt

Therefore this behavior predates `f64a748`.

## Root cause

Field-store extraction in `buildFieldStoreMapFromIR` currently does:

1. `ptr = SI->getPointerOperand()->stripPointerCasts()`
2. `if (auto *GEP = dyn_cast<GEPOperator>(ptr)) getGEPStructField(GEP, ...)`

This interacts badly with nested GEPs:

- For `sub` (index 0), the trailing array-index GEP is all-zero and gets
  stripped, exposing the base struct-field GEP, so evidence is recorded.
- For `up/avg/paeth*` (indices 1/2/3), that GEP is not stripped, so
  `getGEPStructField` mostly sees `[4 x ptr]` and does not recover the parent
  struct field in this path.

Net effect: only `sub` gets a `funcFieldStores` entry and is thus rejected at
callsite field checks; others are conservatively kept.

## Implication

This is a field-store extraction limitation/bug (precision inconsistency), not
a CFL aliasing regression from the recent extern-declaration canonicalization
fix.

## Follow-up ideas

1. Normalize store pointer operands by recursively peeling nested GEP/bitcast
   chains, not just one `stripPointerCasts()` step.
2. In `getGEPStructField`, optionally walk through outer array/vector layers
   and continue to recover innermost named struct field.
3. Add an artificial regression test for nested-GEP store patterns where table
   slots are non-zero indices.

