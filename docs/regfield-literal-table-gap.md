# RegField table discovery misses literal-typed constant tables (UNSOUND)

Status: FIXED 2026-09-12 — witness-by-use implemented in
`runRegFieldGapReport` (CallGraph.cc) plus a `--cfl-filter-ledger`
audit instrument; all answer-level gates below passed. Found
2026-09-12 by the SoK-MLTA fuzz ground truth (eval/62/65/66).

Fix gates (all with the fixed binary, this box):
- nm-new full config: 70,838 icalls (base 83,770; 12,932 pairs
  still soundly filtered); filter ledger joined against the fuzz
  GT = **0 observed records filtered** (was 90+ pre-fix, per-callsite).
- PMU slice: `CLOSED struct.x86_pmu+192 table=3` now includes
  amd_put_event_constraints / intel_put_event_constraints; cert green.
- km (6.8.2 subset, 338 TUs) old-vs-new binary: +4,663/−0 pairs —
  strictly additive; cert 0 violations. Final vintage (with the
  addendum fixes, 24af384): 112,324 = +30 more, still additive.
- httpd FI full: 46,313 = old pin 45,479 +834/−0, ⊆ base, cert
  green; unchanged by the addendum fixes (byte-identical).
- pg FI full: 438,583 = old pin 435,979 +2,604/−0; final vintage
  438,690 (+107 more from the addendum fixes), ⊆ base, cert green.
- cfl-smoke 4/4; libpng cert green (19 ICALLs, 0 FILTERED).
- SoK recall table re-cut (eval/62+65, final binary): ORCFL full =
  100% on every soundness program except cflow O3 (84.21% — full ≡
  base there, and every baseline is sub-100 incl. LLVM-CFI 94.74%:
  a shared corpus/GT artifact, not a mechanism).

Remaining (tracked outside this ticket): kernel 5.18 full-family
matrix re-cut on the big machine; SoK eval/62+65 re-run; usermode
fs pins (fsfull) re-cut via eval/64.

ADDENDUM 2026-09-12 (same day, found by the same ledger+GT
methodology): two more holes surfaced once the literal-table fix
landed —
1. Summary proposers blind to varargs (adoption erased
   sqlite3_config's mem-methods install) — separate ticket,
   docs/summary-varargs-gap.md.
2. Copy-closure empty-source hole (THIS channel): the census
   records key-to-key copy edges (`copyIn`) and propagates
   populations and openness along them, but a copy SOURCE with no
   witnessed population and no openness contributed nothing and
   let the dest close. libjpeg: jinit_upsampler installs
   sep_upsample through my_upsampler+var (blocked: var-off), so
   jpeg_upsampler+8 has stored=0; jdpostct.c then relays
   `post->pub.post_process_data = cinfo->upsample->_upsample` —
   jpeg_d_post_controller+8 closed over a table missing
   sep_upsample and the ledger showed it FILTERED at the three GT
   callsites (djpeg O3). Fix: a copy-in source with an EMPTY
   witnessed population opens the dest (evidence-free is not
   enumerable — the same rule the loose-table absorption already
   applies to outer keys); mirrored in the obj closure. Gate:
   djpeg O3 full == pure-base on the fuzz GT.

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

## Fix design (settled 2026-09-12 with user): witness-by-use

The channel key stays as-is (a unique id; name-derived where the
dispatch GEP provides it). What must change is MEMBERSHIP
WITNESSING, which today conflates identity with the type name.
Attribution becomes value-flow-based (type-of-use, not
type-of-name):

1. A literal (or otherwise unattributable) constant's fn slots are
   witnessed AT ITS USE SITES, reading slots by layout offset of
   the USE context: (a) bulk copy into a keyed destination
   (`x86_pmu = amd_pmu`: the dest struct gives the key; walk the
   const source's initializer at the dest's offsets,
   init-attributed); (b) address stored into a keyed ops-pointer
   field (`store &cache_iovec` into `bfd->iovec`: the obj-channel
   population member's initializer, read by offset, feeds the
   fn-slot keys).
2. The same-type instance-copy rescue may only fire when the
   SOURCE's population is witnessed; an unwitnessed (literal,
   unattributable) source refuses the key. This repairs the YELLOW
   assumption instead of deleting the rescue.
3. Completeness argument (the Lean premise): a constant table can
   only influence a dispatch if its address or contents flow into
   live memory, and every such flow event is an instruction the
   census already classifies (store / copy / install-API hop /
   hazard). Attribute-or-refuse at those events is therefore
   total; a nameless constant with NO classified use is
   unreachable and sound to ignore. No corpus-wide poison needed.
4. Certifier check mirroring the refusal: a key may close only if
   every constant-global source feeding it (copy sources,
   population members) has attributed slots; init=0 keys carrying
   copy/rescue evidence must not close.

Corpus survey (why option "global poison" was rejected): kernel
5.18 = 7 literal fn-tables, all x86_pmu instances (poison would
kill the channel corpus-wide); our httpd/pg clang-18 LTO corpora =
0; the SoK clang-15 -O0 set = common (nm-new 19, ffmpeg 56,
pdftotext 108, Bento4 284). Emission-pipeline-dependent — which is
also why enumerated-spelling (type-name or structural-shape)
discovery can never be made complete.

## Blast radius

- SoK tables: the four rows above; ORCFL `full` rows are INVALID
  until fixed (base rows unaffected). Re-run eval/62 (full config
  only) + eval/65 after the fix; regression gate = nm-new
  `cache_bseek` present and all four programs back at base recall.
- Kernel 5.18: AFFECTED, confirmed 2026-09-12. The corpus has 7
  literal-typed fn-tables — the static x86_pmu instances (amd_pmu,
  core_pmu, intel_pmu, p4/p6/knc/zhaoxin), literal because of the
  anonymous-union member. 15 struct.x86_pmu keys CLOSED in the 5.18
  full run; audit shows init=0 (no initializer witnessing) and
  YELLOW (closed via the same-type instance-copy rescue, whose
  population-preservation assumption is exactly what the unwitnessed
  literal sources violate). Direct FN evidence on the
  arch/x86/events + kernel/events slice: key +192 table =
  {amd_put_event_constraints_f17h} only, while amd_pmu's literal
  initializer holds amd_put_event_constraints at +192 (installed by
  the boot copy x86_pmu = amd_pmu; reachable on every AMD f15
  machine); +88 misses amd_pmu_hw_config; +184 misses plain
  amd_get_event_constraints. ALL 5.18 full-family pins must be
  re-cut after the fix; the frames-based GT never caught this
  (PMU frames absent from the GT set).
- httpd/postgres transfer pins: the "byte-identical" prediction was
  WRONG, in the sound direction. The corpora do contain zero literal
  fn-table constants, but the fix's loose-table definition is wider
  than "literal-typed": any initializer fn slot with no named-key
  attribution counts (httpd has 1,598 such tables, pg 10), and the
  coarse absorption rule (unresolved/open/EMPTY-population outer
  keys absorb all loose tables) adds their entries at apply. Result:
  httpd full 45,479 → 46,313 (+834/−0), pg full 435,979 → 438,583
  (+2,604/−0); both still ⊆ base, certs green. FI transfer pins
  re-cut to the new values; fsfull pins likewise need a re-cut.
