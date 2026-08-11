# Design section (paper-ready draft, 2026-08-08; rev 2 same day)

Drafted after the #46–#48 perf arc closed the measured-lever board.
Rev 2: the pre-design measurements (closure-wall autopsy, boundary
census) moved OUT to §2 (docs/measurement-section.md); this section
now opens from that section's requirements R1–R4. Consolidates the
outline's §3–§7; split at the marked seams if the staircase
organization wins. Citation keys and cross-references are
placeholders; every number cites a pinned baseline or a committed
measurement.

---

# 3. Design

Section 2 left a specification: change what is computed rather than
how fast it is computed (R1), tolerate no silent resource caps (R2),
model or ledger every boundary channel (R3), and make exactness
checkable at a scale where no one reviews the answers (R4). This
section presents a design built to that specification. Its three
axes — **scalability**, **soundness**, **precision** — are three
problems wearing one coat: the closure that explodes and the
may-alias pooling that destroys precision are the same quantity, and
the soundness machinery is what lets the other two axes move
aggressively. Three principles run through everything:

- **P1 — Anchor, don't materialize.** Never materialize the all-pairs
  alias relation; materialize an origin-to-node witness relation whose
  shape is rectangular — origins × reachable nodes — and empirically
  far smaller, with everything pairwise kept implicit in a union-find
  quotient. (This is a structural claim about *what* is stored, not an
  output-sensitive worst-case bound: witness origins beyond the answer
  alphabet are propagated too.)
- **P2 — No silent approximation.** Every shortcut is (a) proven
  exact (machine-checked), (b) certified exact per run, or (c)
  counted in a ledger that a reader can audit. A cap that can fire
  silently is a bug by policy, enforced by assertion.
- **P3 — Measure before building.** Every optimization names the
  redundancy it removes and carries the measurement that found it;
  candidate designs are killed by cheap probes before engineering
  begins. The falsification ledger (Table T3) is part of the design
  record, not an appendix of regrets.

## 3.1 Scalability: from a quadratic closure to answer-anchored facts

R1 rules out both roads already traveled: saturation materializes the
Θ(Σ|C|²) closure that drowned the baseline (§2.1), and per-query
traversal re-pays the shared exploration once per wiring round. What
a call graph needs is a formulation that is whole-program in
*coverage* but demand-shaped in *fact mass* — all demands answered at
once, anchored at the only identities the answers are made of.

**Answer-anchored flows-to (P1).** The reformulation stores no
pairwise facts. Each *origin* — a function, global, or allocation
site whose identity answers are made of — is minted as a root; the
solver propagates *(origin, field-shift)* planes forward over
assignment and field edges. Memory aliasing never materializes:
when two dereference cells share an origin fact at compatible shifts,
their equivalence classes merge in a union-find quotient — the
optimally-solvable bidirected fragment of the language [POPL18] used
as a component — and the merge is *witness-exact*: keyed by the
specific (origin, shift) pair that licensed it, provably lossless
with respect to the CFL relation (machine-checked; §3.2). Fact mass
drops from Σ|C|² to Σ|C|·(answer-relevant origins). The effect is
categorical: the saturation baseline cannot finish a library, while
the flows-to solver completes the 2,618-module kernel — the first
solver-certified whole-kernel run of this formulation (§3.2 defines
the run-status vocabulary) — in twenty minutes.

**Field sensitivity in the weight domain.** C field sensitivity
cannot live in the Dyck parenthesis alphabet: `container_of` demands
that two interior-pointer steps compose to match one flat offset
(down-8 · down-8 ≡ down-16), which exactly-matched parentheses
cannot express — and our attempt to encode composition
grammatically explodes saturation (scaffolding × (P+1) shifts;
measured OOM). Instead, offsets ride the *weight domain*: each fact
carries a shift residue in Z_P — a *sound finite quotient* of exact
signed offsets, not the offsets themselves: modular collisions and
the wildcard ⊤ can only add flows, and the abstraction is
machine-checked as a monoid homomorphism under which derivable
answers remain derivable answers [Lean: `fderiv_shift_hom`,
`zpShifts`]. Because residues are per-fact annotations rather than
graph structure, the encoding is exactly as summarizable as the FI
solver. Field sensitivity is then applied *surgically*: origins
whose types never carry dispatch state mint at ⊤, and the per-root
wildcard policy is itself covered by a machine-checked abstraction
theorem — a widened root's grammar answers all surface at ⊤, which
resolution accepts [Lean: `pol_answers_complete`] — confining
residue cost to the nexus-typed population: 98.3% of full field
sensitivity at one third of its cost.

**Solver engineering as measured redundancy elimination (P3).** Every
optimization in the solver names its redundancy: delta propagation
(re-pushing settled facts); topological wave scheduling (fragmented
*order* — 11–39x on every input, with the diagnosis that cost was
access order, not repeated work); dynamic a-SCC collapse (classes
provably plane-equal at fixpoint); copy-on-write plane sharing
(chains adopt a full-arriving plane in O(1), with detach-on-divergence
keeping exactness); and cluster-mark joins — profiling showed 99.8%
of join lookups were redundant cold probes of the cluster registry,
each re-proving that a cell already belonged to an origin's cluster,
because completion was tracked per-class while join effects are
per-cluster; a monotone mirror of registry outcomes, tested before
the probe, cut registry lookups 414-fold and total solve cycles by a
fifth, with marks that can only be *missed* (conservative), never
wrongly present. The same discipline kills designs: content-hash
interning of planes found that end-state duplication (60% of classes)
does not exist in-flight — planes that converge at fixpoint diverge
temporally on the way — and root bundling died by probe: the
field-sensitive fact mass is concentrated in ~13k exact-residue
origins (~10⁵ facts each) whose divergence is the analysis's
product, not redundancy. [Seam: outline §2/§3 end here.]

**Resource-bounded solving, exactly.** What remains after
reformulation is bounded by turning memory into a dial without
touching answers. Fact planes are pure derived state — the only
cross-origin coupling is the quotient, the cluster keys, and the
bridges — so origins solve in batches: seed K roots, drain, harvest,
release every plane; outer rounds repeat until the retained witness
state is stable — no new merges, no late mints, and no new cluster
keys in a pass — which is precisely the stable-table hypothesis of
the batching theorem, and terminates at the same closure by
monotonicity over a finite universe. Batches run in
forked copy-on-write workers that stream their effectual events
(first-time key inserts, merges) for replay; batch-local fact
universes shrink dense-plane width from whole-corpus to batch width
(42.5 KB → 2.5 KB at kernel scale — the difference between fitting
and the OOM cliff); and completed batches spill to zstd-compressed
snapshots that later rounds restore and top up with only the
cross-batch delta. The spill compresses ~600x — the same replication
that costs RAM is what the compressor removes, one phenomenon seen
from two sides. Every mode — monolithic, batched, worker-parallel,
spilled — is byte-identical to every other at every gate, and the
staged-exactness arguments (catch-up confluence for lazily-minted
roots, batch-union equality, spill-restore confluence) are
machine-checked in Lean *at the declarative-closure level*; the
refinement from event replay, snapshot serialization, and the
touch-window delta schedule to those closures is carried by the
byte-identity gates and named as an open obligation (GAPS.md), not
claimed. "Memory becomes a dial" has a stated floor: the graph,
presolve quotient, cluster registry, and worker multiplicity remain
resident. A kernel-scale field-sensitive solve runs on a 62 GB
desktop.

## 3.2 Soundness: no silent fallback, certified at every layer

**The challenge has two faces.** Outward, the dispatch-fabric census
of §2.2: assembly, integer-laundered pointers, section arrays,
patching families — R3's obligation list. Inward: a solver under
scaling pressure accumulates approximations, and each one is a place
where flows can vanish without a trace. The design treats both faces
with the same instrument set.

**Boundary: the census as a gate, then model-or-ledger.** The §2.2
census is not documentation — it is *enforced*. The
instruction-disposition check runs on every analysis invocation and
aborts on an undispositioned kind; nothing defaults. Each channel
the census names is then either modeled with an explicit witness or
declined into a named ledger counter: pointer-capable assembly
templates get edges derived from their constraint signatures
(immediate-only categories excluded, and said so); integer-carried
pointers get witness-gated pointer-width load/store edges, with
every declined case counted; section arrays receive their own node
identities with closed-world bounds rather than resolving to an
unsound empty or a universal blob; patching families are handled as
identity channels (§3.3), whose completeness counters must read
zero. The extern-boundary census re-runs per corpus as a standing
proof obligation. The ledger is not an apology; it is the audit
surface: a reader can enumerate exactly what the analysis declined
to model and what evidence gates each modeled channel.

**Approximation: proof where theory reaches, certificates where it
does not.** The solver's central invariants are mechanized in Lean
against a derivation-semantics model, with the three merge kinds
kept deliberately distinct. The least solver closure over
exact-seeded roots is *two-sidedly equivalent* to the rooted grammar
— completeness and soundness are separate theorems and both are
machine-checked [Lean: `solver_complete`, `sderiv_sound_fderiv`,
combined in `sderiv_iff_fderiv`]. Witness-keyed cell joins live
inside that equivalence. The dynamic a-SCC collapse and the presolve
component quotient are *sound* (any node quotient preserves
derivability [Lean: `fderiv_quotient`]) but not claimed
precision-neutral: the presolve quotient is deliberately coarse
(§3.3 measures a 41-node mutual-flow core inside a 41,350-node
component), and the a-SCC converse is a pending obligation. Lazy
root minting is exact given a catch-up round (the sufficiency of
propagation loops alone was *refuted* by a kernel counterexample —
circular registration lists create mutual witness dependence — and
the catch-up construction was then proved complete); batched solving
equals the eager closure; spill-restore is confluent; the surgical
wildcard seed policy has its own abstraction theorem [Lean:
`pol_answers_complete`]. The proofs are
load-bearing in both directions: a July minting bug manifested as a
violation of a formal hypothesis before it was understood as a code
defect. Where the model's assumptions meet the implementation, the
run certificate discharges them on the live fixpoint: rule closure
(C0–C5), *seed presence* for every minted root under its mint policy
(C6), and *mint coverage* of the origin criterion at the final
quotient (C7) — together, exactly the abstract theorem's hypotheses,
checked per run. Where the certificate cannot run (batched planes
are released before it could scan them), the strengthened stability
test — no new merges, mints, or cluster keys — plus cross-mode
byte-identity carry the argument, and the paper states which
instrument covers which run. Differential evidence is labeled as
what it is: a −N/+0 comparison proves the new answer set is a
*subset* of the prior one — a regression and precision check — while
*soundness* of each removal is carried by the removing mechanism's
own completeness contract (census counters at zero, closedness
certificates). Configurations outside a validated envelope are
*refused* rather than degraded: incremental solving under field
sensitivity exits with the named divergence, and an outer fixpoint
that would hit its iteration cap before converging refuses to emit
the capped answer set at all.

**Run-status vocabulary.** Every reported run carries one of three
statuses, so "sound" is never a layer-ambiguous word: (i)
SOLVER-CERTIFIED — exact relative to the encoded grammar,
certificate- or byte-identity-discharged; (ii) PROGRAM-SOUND —
additionally, every soundness-relevant ledger reads zero, no
rejecting post-filter is active, and no pointer-capable boundary
case was declined; (iii) AUDITED-INCOMPLETE — known gaps quantified
in nonzero ledgers. The kernel pins in this paper are
SOLVER-CERTIFIED with ledgers reported; the census's declined
channels are precisely the measured distance to PROGRAM-SOUND.

This is R2 made structural: where the state of the art moves its
unsoundness into resource caps at the least-auditable point (§2.1),
this design makes silent approximation unavailable by construction.
[Seam: soundness machinery recurs in §3.1's staging proofs and
§3.3's channel completeness counters; in a split organization this
subsection owns the Lean + certificate exposition, §2.2 owns the
census numbers.]

## 3.3 Precision: understand the quotient, then drain it at the answer layer

**The wall.** Sound field-insensitive propagation pools 93% of
resolved pairs into the cone of a single may-alias class. Anatomy
before surgery (P3): the giant is *born* in presolve — Steensgaard-
style connected-component unification over copy chains; its true
mutual-flow core is 41 nodes of 41,350 — and *sustained* by fact
accumulation through a small set of semantically real rendezvous
channels (task_struct, tracepoint argument pools), not by ongoing
class merging. The kernel's object plane is otherwise bimodally
modular: cross-subsystem welds are 0.98% of merges. This anatomy is
what makes the remedies principled: the quotient is not a bug to
fix but a structure whose irreducible core is the kernel's real
rendezvous fabric — and whose *reducible* mass has specific,
nameable causes.

**Falsifications first: why graph-level refinement fails here.**
Three natural refinements were built and measured before the design
settled. Splitting heap identities regresses (+11k pairs): per-site
objects are hub-resident, and finer identities multiply smear while
the type-erasure hub stands. Carrying (function, data) origin
correlation through the graph is vacuous: cluster merges destroy the
correlation before fixpoint (measured 0.000% excess discrimination).
And per-key channel cells for tracepoints lose the function identity
they exist to protect — it is a casualty of the very V-merges that
make propagation sound. The shared lesson is structural: **once the
quotient has absorbed either endpoint of a dispatch registration, no
refinement inside the graph can recover it.**

**Identity channels: exact bindings consumed at answer level.** The
remedy moves the identity outside the quotient. For each dispatch
family whose registrations are statically enumerable, a census walks
the binding structures the kernel itself maintains — tracepoint key
objects, static_call ops tables, registration-correlated dispatcher
arguments (the INVOKE family: kthread/timer/RCU/IRQ payload pairs;
keyed notifier chains) — into a complete binding table, and
*resolution* consumes the table directly while the graph-level pool
is severed. Two disciplines keep this sound. Completeness counters:
every construct the census cannot classify is counted, and the
counter must read zero for the channel to activate — a nonzero count
is a loud failure, not a fallback. The completeness contract is what
carries each channel's *soundness* — producers enumerated, updates
represented, consumers recognized, no severed alternate path — and
the −N/+0 differential against the prior baseline is its *regression
check*: proof that the channel only removed, never what it removed
was false. The two
largest channels remove 1.50M and 1.20M pairs (32% of the pinned
answer set combined) while making the solve *faster*, because the
severed pool no longer propagates.

**Automating the channel tier.** The hand-built channels have a
common signature that turns out to be *detectable from a single
field-insensitive run*: a (struct, offset) registration field whose
*witnessed store population* is narrow while the resolved fanout at
its reader sites is wide — the gap is exactly the pooled smear a
channel would remove. A post-solve detector gathers each field's
population from four sources (constant stores, one argument hop for
install-API shapes, global-initializer slots, and a copy-closure
between field keys for control-struct relays), and a *closedness
certifier* decides, per key, whether that table is provably
complete: every mutation path classified, and five hazard counters
at zero (unwitnessed stores, atomics on the slot, bulk copies from
non-constant sources, escaping slot addresses, variable-offset
keys). Closed keys become channels in the same run — resolution at
their reader sites intersects with the table; open keys are never
touched, because same-slot instance pools look exactly like an
unwitnessable population and must be left to the graph. On the
kernel this removes a further 1.49M pairs (−30.6% *on top of* the
hand-built channels) across 1,997 auto-certified keys in 8,089
sites — the long tail of driver ops families no one would hand-
build — at *negative* solve cost, with the median site fanout
falling from 43 to 6 and the giant's hubs untouched (their keys
correctly refuse to close). The discipline transfers with the
automation: every applied key emits a provenance certificate
(1,105 of 1,997 tables are const-initializer-only — closedness is
rodata-structural; the copy-closure-dependent tail is 23 keys),
the certifier's one blind spot (function stores through bare
untyped pointers) is a counted ledger line (273 kernel-wide), and
the audit that hardened it — a whole-struct-store shape that was
invisible *and* unhazarded — de-closed exactly one kernel key and
restored 572 true-risk pairs, the false-negative class caught
before it shipped.

**Semantics by data, not by name.** Transfer summaries
(FRESH/CPY/ALIAS/ST/LD/NOOP atoms, plus the dispatch-binding atoms
above) replace the inherited name-heuristics for allocators and
utility functions; when the summary file is loaded it is
authoritative, and the legacy name lists survive only as a bare-run
fallback. This closed a real soundness hole the heuristics had
created (a prefix skip-list silently dropped whole function bodies —
including the RCU callback dispatchers — making every `call_rcu`
callback invisible; the fix is exact-name, audited, and recovered
+1,038 pairs of pure recall at km). Type and field compatibility
remain in the pipeline but demoted to *post-filters* over
flow-confirmed candidates, each rejection counted as explicit
unsoundness exposure. Counting makes the exposure visible; it does
not make filtered output sound — a PROGRAM-SOUND configuration
(§3.2) disables the rejecting filters or conservatively retains
their rejects, and the counters price exactly what that switch
costs. They are the retirement criterion, not a trust assumption.

**Field sensitivity as a precision instrument.** The surgical
residues of §3.1 are also the precision story's second act, and the
same-binary kernel A/B fixes its *size*: selective fs removes ~1.7%
of pairs at ~20–30x the solve cost, against the channels' 30%+ at
negative cost — because the pool's dominant conflation is
same-offset registration mixing, which offsets cannot discriminate
(the ~2% that fs does remove is the cross-field artifact mode, and
its deep collapses are precisely the sites the channel detector
finds for free). What remains fs's own: residues discriminate
within the pool (the fs decomposition attributes ~30% of the
discrimination to identity residues on shared-helper formals), and
member-to-container composition can derive true pairs FI cannot —
verified at micro scale (t_container, t_allocinit); at km the HEAD
same-binary A/B measured *zero* fs-only pairs, so the recall claim
is stated at the scale it is proven and the kernel-scale
verification is an explicit open item. fs's load-bearing role in
the final design is the *instrument*: it produced the anatomy, the
decomposition, and the reference answer sets that the cheap layers
are certified against.

## 3.4 One problem, one currency

The three challenges are coupled through a single quantity: closure
cost and precision loss are both governed by Σ|C|² over the may-alias
quotient, and the quotient's shape is set by *identity co-occurrence*
— a property of source idioms, not of solvers. That is why the design
routes every axis through the same object: the code-idiom →
graph-structure → solver-bottleneck catalog (Table X) traces each
kernel pattern (shared rodata witnesses, allocator wrappers, circular
registration lists, void*-payload rendezvous, container_of
composition, patching families) to the pathology it induces and the
layer that must absorb it. Scalability work changes what is
materialized about the quotient; precision work changes what the
quotient is allowed to absorb; and the soundness machinery is what
lets both move aggressively — a transformation that must be
byte-identical, certified, or refused can be adopted without a
leap of faith. The same ladder points forward: because every
approximation is witnessed, the analysis can carry *stratum
separation* obligations (no flow from user-controlled or payload
memory into indirect-call resolution outside a reviewed crossing
set) as checkable certificates rather than assumptions — precision
and provability climbing the same stairs.

---

## Notes for the writer (not part of the section)

- Rev 2 split: wall autopsy + boundary census numbers now live in
  §2 (docs/measurement-section.md); this section references R1–R4
  and keeps only design-side numbers.
- Numbers used and their pins: first whole-kernel
  14,799/5.1M/~20min (kernel-full3); canonical pin 18,189/5.69M/2.98h
  (kernel-idchan); NEW 6.18 big-machine baselines (2026-08-10):
  kernel-fi-618 4,866,847/16,512/2:07 and AUDITED auto-channel pin
  kernel-fi-autochan2 3,379,430 (−1,487,417/+0, 1,997 keys, fanout
  p50 43→6, 1:46, certificates 1,105 GREEN/869 YELLOW/23 ORANGE,
  residual 273, hole-fix restored 572 @search_nested_keyrings);
  kernel fs completion 70h20m/365GB (old binary — feasibility pin
  only); fs-worthiness A/B: genuine fs tightening −1.66%
  (80,868 @7,694 sites, 73 deep-collapse sites = 18,376 pairs);
  km targeted-fs verdict 60% capture at ~0.8x all+ids cost (NSHIFT-
  structural floor) → channels won; wave 11–39x; #48 lookups
  39.94M→96k / cycles −21.5%; fs surgical 98.3%@1/3 cost +
  identity-residue 30% (task #39); batch width 42.5→2.5KB, spill
  ~600x, 62GB desktop; identity channels −1.50M/−1.20M = 32%;
  anatomy 41/41,350, 0.98% welds, 93% giant; #44 recall +1,038 (km);
  falsifications: dedup×2, folding, delta re-offer, heap-split +11k,
  origin-split 0.000%, tracepoint cells v1/v2, lazy-mint A-loop
  refutation, #7 in-flight duplication, #8 fs bundling. Cross-check
  all against the stats files before submission; km numbers are
  subset-scale evidence, kernel numbers are the headline scale —
  keep the distinction explicit in prose.
- If the staircase organization wins, the seams marked [Seam] split
  this into outline §2/§3 (scalability), a soundness-methodology
  section, and §4–§5 (anatomy + channels); 3.4 becomes the closing
  of the design part either way.
- Lean scope honesty: cite proof/lean/GAPS.md (event-replay
  fidelity, touch-window delta completeness, termination) wherever
  "machine-checked" appears in final prose.
