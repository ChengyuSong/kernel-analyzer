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

ACTION (final, 2026-09-04): REMOVED outright under the
fix-or-remove policy — feature, flags, and the witness-taint
subsystem deleted; no tombstone. The re-admission bar is the Lean
spec `Incr.incr_exact` (proof/lean/CompositionalCFL/Staging.lean):
any future incremental implementation must discharge
`delta_seeds_complete` — every newly wired rule instance whose
premises are all old facts gets its conclusion seeded — which is
exactly the clause this bug violated (newly wired call edges from
iteration >= 2 connecting old actual-facts to old formal-cells had
no fresh premise, so nothing fired). Canonical pins are
from-scratch: full = 6,291,136, base = 15,796,198.

REPLACEMENT VERIFIED (2026-09-04): full stack + --cfl-lazy-mint +
--cfl-bidi-prune, from scratch = 6,291,136 pairs (sha 38764d36…),
a strict superset of the removed mode's pin by exactly the 2,032
dropped pairs (+2,032/−0, comm-verified). Solve walls: 7,248s vs
8,764s plain scratch vs 5,915s for the removed mode — about half
the win recovered, at zero soundness debt (both levers have
machine-checked exactness/soundness statements and carry no
cross-iteration state). This is the recommended configuration;
eval/60-kernel-fse.sh gates it byte-identical to full (`lazybidi`
arm).
