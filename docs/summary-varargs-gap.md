# Solved/atom summary proposers were blind to varargs (UNSOUND)

Status: FIXED 2026-09-12, same day as found. Found by the
`--cfl-filter-ledger` methodology from the regfield campaign
(docs/regfield-literal-table-gap.md): after that fix, the SoK fuzz
ground truth still showed ORCFL `full` below `base` on
sqlite3__fuzzershell (O0 99.09%, O3 98.71%). The ledger proved no
clamp removed the pairs (0 mentions across 8,524 FILTERED lines) —
so they were never DERIVED, which moved suspicion from the filters
to the summary mechanisms. Arm bisection: base+adopt loses all 24
records; base+chain and base+regfield lose none.

## Root cause

`SolvedProp: OK-EMPTY sqlite3_config`. sqlite3_config is varargs:

    sqlite3GlobalConfig.m = *va_arg(ap, sqlite3_mem_methods*);

The solved-summary pass runs a local abstract interpretation of the
body and proposes a summary from the solution. Its intrinsic switch
treated `va_start`/`va_copy` as benign no-ops (same list as the
noop pass), so the local va_list was never connected to caller tail
args; the va_arg load then read cells the interpreter tracks as
EMPTY, the memcpy into sqlite3GlobalConfig moved "nothing", and the
function solved to an EMPTY summary. Adoption then erased the real
install: every sqlite3_mem_methods / sqlite3_pcache_methods2 member
disappeared from the answer (24 fuzz-observed records).

The atom pass (`AtomProp`) had the identical blind spot (it happened
to refuse sqlite3_config for [store-target], but that is luck, not a
guard). The noop pass is safe WITHOUT a varargs guard: a noop
summary can only be unsound if content leaves the function, and
NoopProp already refuses every pointer store, callee call, icall,
and pointer return.

## Fix (attribute-or-refuse)

`va_start`/`va_copy` now REFUSE in both the atom and solved
proposers ([varargs] refusal class): a function that reads caller
tail args has effects the local solve cannot enumerate. `va_end`
stays benign (no data flow). The main solver models vararg
actual-to-formal wiring, so refusal restores exact base behavior
for these functions.

## Gates

- sqlite3 O0 base+adopt: 24 GT misses -> 0; `SolvedProp: REFUSED
  sqlite3_config [varargs]`.
- sqlite3 O3 / nm-new O0 / djpeg O3: full-config == pure-base on
  the fuzz GT (remaining strict-matcher deltas are shared with base
  and score 100% under their compare).
- cfl-smoke 4/4; libpng closure cert green.
- httpd/pg/km full re-cuts: see the regfield ticket's gate table
  (this fix shifts answers additively — refused summaries mean more
  derived pairs, never fewer).

## Lesson

A summary proposer's totality premise ("the local solve sees every
effect") must enumerate its blind spots explicitly. Varargs was an
IMPLICIT blind spot shared by two of three proposers; the third was
safe only because its other refusals happened to cover it. The
census/certifier discipline (attribute-or-refuse, with a stated
residual) applies to summary proposal exactly as it does to
channel closure.
