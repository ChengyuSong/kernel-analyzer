# RegField table discovery misses literal-typed constant tables (UNSOUND)

Status: OPEN — certifier gap, found 2026-09-12 by the SoK-MLTA fuzz
ground truth (eval/62/65/66). Fix required before the regfield
channel's results ship; design-first per the soundness discipline.

## Symptom

ORCFL `full` scores below `base` on dynamically-observed recall
(their fuzz ground truth = executed indirect-call targets):

| program (SoK soundness set) | full | base |
|---|---|---|
| nm-new (binutils) O0 | 69.96% | 100% |
| sqlite3__fuzzershell O0 | 99.09% | 100% |
| sqlite3__fuzzershell O3 | 98.71% | 100% |
| libjpeg-turbo djpeg-static O3 | 98.67% | 100% |

A precision mechanism removed pairs that fuzzing OBSERVED. Ablation
bisection on nm-new.bc, both directions, single cause:
- removal side: only the `noregf` arm recovers the missing targets
  (`cache_bseek`: full 0 pairs, noregf 2); noadopt / nochain /
  noopstables / noinvoke all reproduce full exactly (14,342 pairs).
- additive side: base+regfield ALONE reproduces full's answer count
  exactly (83,770 → 14,342) and drops `cache_bseek`; base+chain and
  base+adoption leave base unchanged (chain and adoption are inert
  on this program).

## Root cause

The regfield channel certified bfd's iovec keys as CLOSED with a
2-entry table:

    RegFieldChannel: CLOSED struct.bfd_iovec+48 table=2 sites=1 -111/+0 kept=1

but nm-new has THREE iovec implementations. In the IR:

    @opncls_iovec      = internal constant %struct.bfd_iovec.148 {...}
    @_bfd_memory_iovec = internal constant %struct.bfd_iovec.219 {...}
    @cache_iovec       = internal constant { ptr, ptr, ... } { ptr @cache_bread, ... }

`cache_iovec` is emitted with an ANONYMOUS LITERAL struct type —
clang does this when the initializer's type does not exactly match
the declared struct (mismatched fptr prototypes under opaque
pointers). The census discovers candidate tables BY NAMED STRUCT
TYPE, so it saw two of three tables, certified the key complete,
and removed every `cache_*` target from `abfd->iovec->…` dispatches
(`bfdio.c:337` etc.) — all fuzz-observed.

## The violated premise

Table-completeness discovery assumes: *every constant table that
can flow into a dispatch base of struct type S is discoverable as a
global of named type S*. False — literal-typed constants alias S
structurally and flow into `S*` fields (`store ptr @cache_iovec,
ptr %bfd.iovec.addr`) without ever carrying the name.

## Fix directions (decide, model, then implement)

1. **Certifier-side refusal (minimal, always sound):** while
   certifying key (S, off), enumerate address-taken literal-struct
   constants structurally compatible with S (same slot count/kinds,
   fptr at off). If any exists that is not in the table, REFUSE the
   key. Mirrors the cert-incident lesson: every solver optimism
   needs a matching verifier check.
2. **Flow-based table discovery (keeps precision):** collect
   candidate tables from what actually flows into `S*`-typed bases
   (stores of `&table` into fields/params that reach the dispatch
   base), independent of the constant's own type; structural-match
   literal constants extend the table (over-inclusion is sound).

Either way the premise must be stated in the hazard contract and
reflected in the Lean channel model (same bookkeeping as the
adoption×regfield store-completeness item).

## Blast radius

- SoK tables: the four rows above; ORCFL `full` rows are INVALID
  until fixed (base rows unaffected). Re-run eval/62 (full config
  only) + eval/65 after the fix; regression gate = nm-new
  `cache_bseek` present and all four programs back at base recall.
- Kernel 5.18/6.18 pins: no observed damage (noregf arm has the
  same GT FN count as full; frames-based GT), but the hazard is
  present in principle — a literal-typed ops-table constant in the
  kernel corpus would be missed the same way. State in the paper's
  soundness discussion once fixed; re-run the kernel noregf
  comparison after the fix as confirmation.
- httpd/postgres transfer pins: one-sidedness holds by
  construction; independent GT not available. Same re-check logic
  as kernel applies.
