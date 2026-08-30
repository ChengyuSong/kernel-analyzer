# External review triage (ChatGPT, 2026-08-30, on the pre-campaign design)

The review targets the design docs BEFORE the 2026-08 precision
campaign. Verdict up front: the algorithmic assessment is right, the
claim-discipline critique is largely right — and the campaign
independently validated several of its warnings the hard way before
we read them. Triage of all 16 points against current state:

## Already answered — by the campaign itself (empirically)

- **"−N/+0 over-reliance" — CONFIRMED BY US, TWICE.** The supplement
  policy (+32,575 with every per-key ledger reading −N/+0) and the
  first regfield GT gate (79→90 with 2,299 certified keys) are our
  own demonstrations that removals-only is a regression check, not
  soundness. The discipline moved accordingly: GT FN-identity (79
  list, aux-matched) is the bar; −N/+0 is necessary, never
  sufficient. Research log #57/#59; the paper will present it exactly
  as the reviewer suggests, with our own failures as the evidence.
- **"Channel completeness contract" — EXISTS, NOW EXPLICIT.** The
  hazard machinery IS the contract: producers = witnessed stores +
  initializer slots + install hops + copy closure; unknowns (atomics,
  escapes, unknown-source bulk, variable offsets, writable members,
  bare-pointer stores) leave keys OPEN; alternate paths stay active
  (channels are additive at dispatch; pooled wiring retained);
  containment is per-key ledgered. Formalized as the hypotheses of
  Channels.lean clamp_sound/objclamp_sound — the contract is the
  theorem statement.
- **"Circular validation of auto-discovered channels" — ALREADY THE
  ARCHITECTURE.** The regfield detector uses solved fanout ONLY for
  ranking (the FLAG heuristic); populations and closedness come from
  the independent syntactic scan. Exactly the recommended split;
  needs stating in the paper, not building.
- **"Origin bundling stale" — reported precisely as recommended**
  (semantic success, performance failure, superseded by batching;
  parked with post-mortem). docs/origin-bundles-design.md.

## Already answered — by the 2026-08-11 review response (Codex)

- **Resource caps**: default REFUSES and exits 1; --cfl-iter-cap-ok
  is opt-in with UNSOUND-RISK labeling. Remaining nit adopted: the
  label becomes AUDITED-INCOMPLETE in reporting vocabulary.
- **Byte-identity as proof**: already demoted to regression evidence;
  the batching theorem (batched_exact) is the guarantee, byte-checks
  are its per-run witness. Stated in implementation.md.
- **Lean vs implementation blur**: GAPS.md is the refinement-
  obligation ledger the reviewer asks for; kept current through the
  campaign (rodata assumption, witness-taint retirement).
- **Signed-offset instance**: still OPEN (tracked since 2026-08-11 as
  F12-adjacent). Correctly listed as a trusted obligation.

## Valid and adopted now (doc edits, this commit)

- **Explicit semantic target + non-goals** (the review's #1): the
  rooted relation and answer set are now stated formally in the
  novelty doc, with the four explicit non-goals (no all-pairs CFL, no
  complete Andersen sets, least rooted relation for icall resolution,
  origins kept as witnesses). FlowsTo.lean's header already carried
  the honest rooted-vs-saturation distinction ("unrooted valley
  apexes... legitimately over-approximate"); the prose now matches.
- **Layered guarantee vector**: adopted as the per-run label
  ⟨closure, abstraction, boundary, reporting⟩, e.g.
  CLOSED / OVERAPPROX / LEDGERED / UNFILTERED. Maps onto existing
  machinery: --cfl-verify-closure (closure), quotient direction
  proofs + conservative converses (abstraction), unsoundness ledger +
  SummaryCheck (boundary), filter policy (reporting).
- **Union-find ≠ transitive may-alias**: clarification added — the
  quotient equates internal cell consequences licensed by witness
  rules; it is not a materialized alias relation. (The campaign's
  master formulation already reframes it: the quotient IS the
  imprecision, deliberately coarse.)
- **POPL'18 scoping**: near-linear bidirected-Dyck applies to the
  presolve/bidi fragment only; no complexity claim for the full
  solver. Novelty doc §1 sharpened.
- **"Model-closed" phrasing**: adopted. Note the classifier-totality
  concern is partially discharged by machinery: --ir-census-strict is
  a closed-world gate (any undispositioned construct aborts the run),
  so zero ledger counters mean "model-closed under stated LLVM/arch/
  build/corpus assumptions with a TOTAL classifier," which is the
  defensible sentence.
- **Filtered vs unfiltered answers**: adopted as reporting policy —
  the sound answer set is pre-type-filter; the filtered set is the
  high-confidence view. Instrumentation for the gap already exists
  (--cfl-census-type-rej per-site inventory; --cfl-gt-type-census
  found witnessed filter unsoundness once — the certified static_call
  +29). Paper reports both.
- **Per-number config attribution**: adopted as a hard rule for the
  paper; the pins discipline (flag-match, corpus, baseline, sha) is
  already the internal practice — every table row carries its pin.

## Partial pushback (recorded, not disputed loudly)

- "Rooted presented as equivalent to saturation": the Lean model has
  been explicit about this since sderiv/FlowsTo (rooted = the honest
  runtime semantics; saturation over-approximates on unrooted
  apexes). The docs lagged the proofs; fixed, but the guarantee was
  never claimed in the strong form in the mechanized layer.
- The review predates the campaign: the identity-channel section it
  critiques has since acquired GT gating at every step, the object-
  population re-founding, the master formulation, and a terminal
  fixed-point result — the "main precision contribution" framing it
  recommends is now the measured reality (kernel −60%, httpd −44%,
  pg −63%, GT recall up).

## Reviewer's "keep unchanged" list — unchanged

Formulation-over-optimization, shared work across queries, refusal of
silent caps, measurement-driven falsification (ledger now 13
entries), registration identity outside the quotient, declarative
proofs + per-run closure checks, and the public proof-gap ledger all
survived the campaign and are its spine.
