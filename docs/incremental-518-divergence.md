# FI incremental divergence at linux-5.18 (2026-09-04)

Found by the ablation matrix's perf-family byte-identity gate
(eval/60-kernel-fse.sh): the scratch arm (incremental OFF) produced
6,291,136 pairs vs the incremental-on reference 6,289,104.

Isolation (same binary both sides, big-machine incremental vs local
from-scratch):
- base     (no mechanisms):        -4,394 / +0
- noadopt  (chain+regfield):       -2,364 / +0   -> adoption exonerated
- full     (everything):           -2,032 / +0   -> channels MASK part
Two independent from-scratch witnesses (scratch, lazymint) are
byte-identical to each other.

Missing class (stable across configs): callback-argument flows —
`error` (~565, decompressor callbacks), `flush_buffer` (~376),
`netfs_rreq_copy_terminated` (~322), i915 `insert_pte`/`xehpsdv_*`
(105 each). Real pairs, expected GT-invisible.

VERDICT: the #43 km-FI exactness validation does not transfer to
5.18; the bug is in incremental cross-iteration reuse itself, not
in any mechanism interaction. Sibling of the fs -504 divergence
(km, opt_pre_handler) — likely one root cause: late-round wiring
(icall-resolved callsites gaining edges in iteration >= 2) whose
downstream flows the touched-set fails to re-derive.

ACTION (shipped): auto-on RETIRED; opt-in prints a KNOWN-DIVERGENT
warning. Canonical pins are from-scratch:
  full = 6,291,136 (= scratch arm), base = 15,796,198.
OPEN TICKET: exactness repair — reproduce at a small slice (the
decompressor error-callback family is the candidate: pick the
unlzo/unzstd TUs + their caller), then audit the cross-iteration
touched-set against newly wired call edges. Post-deadline.
