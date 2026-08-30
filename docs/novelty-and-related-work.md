# Novelty ledger and related-work positioning (2026-07-18)

Honest classification of the flows-to (ORCFL) work: what we
rediscovered from the literature, what instantiates known frameworks,
and what we can defend as novel. Written after reading Chatterjee,
Choudhary & Pavlogiannis, *Optimal Dyck Reachability for
Data-Dependence and Alias Analysis*, POPL 2018 (popl18b.pdf in repo
root) against our results log (cfl-graph-explosion-and-scaling.md).

Caveat: literature knowledge is as of early 2026 and was NOT verified
by a fresh search; see "Diligence before drafting" at the end.

## 0. The semantic target — formal statement, non-goals, guarantee vector (2026-08-30)

Added after the external claim-discipline review (see
docs/review-chatgpt-2026-08-30.md). Everything below was already the
operational practice; this section makes it the stated claim so no
reader can attribute a stronger one to us.

**The relation we compute.** Over the linked IR graph G, define the
rooted flows-to relation

    F_G(o, v, δ)  —  "origin o flows to node v with net field shift δ"

as the least relation closed under the solver's derivation rules
(assign/deref valley grammar with Z_P shift weights, seeded at
origins: allocation sites, function addresses, globals). The client
answer per indirect callsite c is

    Ans_G(c) = { f : Function | F_G(f, ptr(c), δ) for an
                 answer-accepting shift δ (identity residue, or any
                 residue when the site is shift-ambiguous) }

**Non-goals (explicitly NOT claimed).**
1. Not all-pairs CFL reachability — we never materialize the full
   V/M relation; the closure-size law (§ below) is precisely why.
2. Not complete Andersen points-to sets for arbitrary pointers —
   only origin facts are stored, and only function-typed origins are
   answer-bearing for the callgraph client. Data-object facts exist
   as witnesses, not as a queryable points-to API.
3. Rooted, not saturated. The mechanized model (FlowsTo.lean) is
   explicit that saturation over-approximates rooted derivations at
   unrooted valley apexes; the shipped solver computes the rooted
   relation, and byte-level pins are pins OF the rooted relation.
4. Soundness is model-relative: "F_G over-approximates runtime
   dispatch" holds under the stated boundary assumptions (assembly,
   extern symbols, arch/build config, corpus completeness), each of
   which is either summarized, ledgered, or refused — never silent.

**The quotient is not may-alias.** The union-find memory layer
equates (origin, shift) CELL CLASSES whose joint consequences the
witness rules license; it is machine-checked fact-equivalent to the
grammar's per-witness M relation (the POPL'18-style lemma pair). It
is NOT a materialized transitive may-alias relation over program
expressions, and no such relation is claimed or exported. Under the
master formulation (kernel-precision-killers.md §8) the quotient is
the single deliberate over-approximation — the address partition —
and every precision lever is a re-indexing of that partition.

**Layered guarantee vector.** Every reported run carries a
four-component label ⟨closure, abstraction, boundary, reporting⟩:
- closure: CLOSED (per-run closure certificate C0–C5 /
  --cfl-verify-closure passed) vs AUDITED-INCOMPLETE (a cap fired
  under explicit opt-in --cfl-iter-cap-ok; default REFUSES).
- abstraction: OVERAPPROX (quotient direction proven; converse
  handled conservatively) — the permanent value for this design.
- boundary: LEDGERED (unsoundness ledger + SummaryCheck counters
  reported; zero counters + --ir-census-strict = model-closed with a
  TOTAL construct classifier under stated assumptions).
- reporting: UNFILTERED vs FILTERED. The sound answer set is the
  PRE-type-filter set; the type filter is a precision view that can
  in principle remove true targets (measured via
  --cfl-census-type-rej / --cfl-gt-type-census, which caught exactly
  one witnessed instance: the certified static_call +29). Paper
  tables state which view each number is, and pair them where the
  gap matters.

**Per-number attribution rule.** Every quantitative claim names its
configuration (flags, corpus, binary vintage, baseline pin + sha).
No mixing of numbers across configs in one sentence; speedups are
same-answer (byte-identical or theorem-covered) or labeled
different-answer.

## 1. Consistency with POPL'18 (Chatterjee et al.)

Their results and our empirical findings agree everywhere they
overlap — and in two places their theory retroactively explains
results we obtained experimentally:

1. **Bidirected Dyck reachability is an equivalence, optimally
   computed by union-find (their `BidirectedReach`, O(m + n·α(n)))**.
   Our phase-1 solver rewrite independently converged on exactly this
   skeleton for the memory layer: exact (o,s) cell clusters merged by
   union-find; merge() splices the loser's edge/cell lists onto the
   keeper (their "gather outgoing edges at the new representative");
   compactLists tolerates duplicates like their linked-list merging;
   the Lean-proved fact-equivalence of cluster transitivity vs the
   grammar's per-witness M is their Soundness/Completeness lemma pair
   (3.1/3.2) in our setting. The solver-side note "bidirectional join
   copies ≡ union-find merges of cell clusters" IS their theorem.
   SCOPE (claim discipline, 2026-08-30): their near-linear
   O(m + n·α(n)) bound applies to the BIDIRECTED-DYCK FRAGMENT only —
   in our solver, the memory/join layer and the bidi presolve. The
   composite solver (directional a-edges + shift weights + rooted
   propagation) inherits NO complexity guarantee from it, and we
   claim none; point 3 below is why none is available.
2. **The partition is cheap; the pairwise relation is the cost.**
   `BidirectedReach` computes the reachability partition in O(m)
   space and never materializes all pairs. Our measured diagnosis —
   saturation OOM = closure size ≈ Σ|a-component|², while joins are
   union-find-cheap in every profile — is the same statement made
   empirically. ORCFL flows-to = keep the partition implicit
   (clusters), store only the answer projection (origin facts).
3. **General (non-bidirected) Dyck is BMM-hard, even at constant
   treewidth.** Our full language is not bidirected (value-flow
   a-edges are directional), so no uniform near-linear algorithm is
   available for the composite problem; output-sensitivity (the
   answer-relevant-root measurement: ~14% of roots, 10-22% of fact
   mass suffice) is the principled escape, not a hack. The
   constant-treewidth hardness also tempers hierarchical/
   tree-decomposition hopes — consistent with our graph-folding
   negative and wide kernel module boundaries.
4. **Their Lemma 3.4 potential argument** (every Union strictly
   shrinks total edge-list mass — merges pay for themselves) is the
   amortization our merge path currently violates: jdirty |= R
   re-offers the keeper's full fact set (subset: 121M re-offered vs
   26.4M final facts, 4.6x overshoot). Theory says a potential-bounded
   join layer exists → independent support for retrying delta-precise
   merge re-offers now that joins are 63% of kernel cycles.
5. **Their field model is Java.** Fields as exactly-matched Dyck
   parens on bidirected SPGs cannot express container_of /interior
   pointers (down-8 · down-8 must match down-16) — precisely our
   2026-07-07 unsoundness bug with flat field buckets, with
   test/t_container.c as witness.

## 2. Rediscovered — cite, claim no novelty

| ours | literature |
|------|-----------|
| join layer: union-find cell clusters, edge-list splicing | Chatterjee et al. POPL'18 `BidirectedReach`; Zhang et al. PLDI'13; collapsing back to Fähndrich et al. |
| wave scheduling (topo ranks over Tarjan condensation, rank-sorted draining) | Pereira & Pearce, *Wave Propagation* (CGO'09) for Andersen |
| delta/difference propagation | Pearce et al.; Datalog semi-naive |
| dynamic a-SCC collapse | online cycle elimination (Fähndrich '98), lazy/hybrid cycle detection (Hardekopf–Lin '07) |
| answer-anchored propagation (propagate origin identities) | Andersen's worldview; demand-driven CFL lineage: Heintze–Tardieu, Sridharan–Bodík, Zheng–Rugina, Boomerang |
| shift labels composed along paths | weighted pushdown systems (Reps–Schwoon–Jha) with weight domain Z_P |

Our 11–39x wave-scheduling numbers and the "cost was ORDER, not
redundant work" falsifications are new *evidence at CFL-plane
granularity*, but the ideas are established Andersen engineering and
must be presented as adaptations.

## 3. Defensible novelties

1. **Witness-exact unification inside a directional solver.** The
   composite architecture: directional origin-fact propagation on
   top, DSCC-style union-find memory layer below, coupled by
   per-(origin, shift) witnesses — with the coupling proven LOSSLESS
   wrt the CFL relation (fact-equivalence, machine-checked), not
   Steensgaard-lossy. Closest ancestor is Das's one-level flow
   (inclusion above, unification below), whose unification sacrifices
   precision; ours provably does not, and POPL'18's equivalence
   theorem is the *reason* it cannot. Their optimality result is used
   as a component-correctness argument inside a problem their own
   hardness result says stays hard in general.
2. **Sound C field sensitivity as a quotient group (Z_P shifts in the
   weight domain), viable at scale.** Dyck field parens cannot host
   container_of; and we measured that the *sound* Dyck-field grammar
   explodes saturation (scaffolding × (P+1) shifts; harfbuzz OOM at
   49GB) while the shift-plane encoding stays flat. Claim: for C,
   field sensitivity belongs in the weight domain, not the
   parenthesis alphabet. Expressible in WPDS; not previously shown
   sound for interior pointers and viable at kernel scale.
3. **Certificate-carrying production runs as the soundness
   methodology.** Per-run closure certificates (C0–C5) discharging
   the mechanized solver model's central assumption; pinned per-icall
   differential baselines; parked-root exemptions with an explicit
   retirement argument; the unsoundness ledger + filter-exposure
   counters as the filter-retirement criterion. Kernel-callgraph
   literature (MLTA/TypeDive lineage) offers none of this and its
   unsoundness is unquantified.
4. **The measurements.** (a) closure-size law on IR graphs with named
   kernel idioms driving component size; (b) root co-travel bounds
   (42% identical incidence columns); (c) answer-relevant root
   fraction with a *sufficiency construction* (function roots ∪
   ancestor-merge witnesses), not a heuristic; (d) the
   falsified-hypothesis catalog (in-flight dedup ×2, deferred joins,
   incremental at kernel scale, parallel-at-kernel-scale) each with a
   measured mechanism. Negative results with causes, in a field that
   mostly publishes speedups.
5. **1-bit VX provenance**: enforcing the grammar's non-transitive
   wildcard exchange pairwise (bridges) without hub transitivity; no
   known analog.

## 4. Paper framing

Lean into the rediscoveries: "the optimal bidirected-Dyck algorithm
and Andersen's best engineering are the right COMPONENTS; we prove
the composition exact where theory permits, certify it at runtime
where theory is silent, and measure what the kernel actually
requires." Rename internal vocabulary to the literature's terms:
joins → DSCC maintenance; wave scheduling → topological difference
propagation; flows-to → answer-anchored (inverse) points-to.

The one-sentence claim (narrowed per the 2026-08-30 review): a
client-specific ROOTED pointer-flow formulation for kernel indirect
calls — sound field sensitivity in the weight domain, registration
identity as channel keys outside the address quotient — where every
guarantee is carried by explicit evidence (mechanized lemma, per-run
certificate, or ledger), not by construction folklore. NOT a general
CFL-reachability engine claim, NOT a complexity claim, NOT complete
points-to.

## 5. Diligence before drafting related work — SURVEY TRIAGED 2026-08-30

An external literature survey (ChatGPT, user-supplied 2026-08-30)
covering the field through Aug 2026 was triaged against the claims
above. Provenance caveat: items at 2026 venues (SQUID/OOPSLA'26,
CAT/ICSE'26, TnFix/ECOOP'26, FastMatrixCFPQ) are past our verified
knowledge (Jan 2026) — VERIFY the papers exist as described before
citing. The pre-2026 items (POCR, PEARL, FLARE, STG, skewed
tabulation, MoYe, MCFL POPL'25, dynamic Dyck POPL'24, KallGraph,
Li'23) match verified knowledge.

**Collision verdicts — all five claimed novelties SURVIVE:**
1. Witness-exact unification: no survey entry couples exact
   union-find beneath directional propagation with a lossless proof.
   The whole solver line (SQUID relation chaining, CAT context-aware
   tabulation, STG staging, skewed tabulation, PEARL/POCR,
   FastMatrixCFPQ) optimizes evaluation of the SAME relation.
2. Z_P field sensitivity in the weight domain: nothing in the survey
   places field offsets in a group weight domain or handles
   container_of soundly. Nearest non-colliders to cite as contrast:
   STG (stages the grammar but keeps field parens as parens), SPDS
   POPL'19 and MCFL POPL'25 (multiple stacks — and MCFL is an
   UNDERapproximation, the opposite soundness pole from us),
   KallGraph's per-path byte-offset stack (already in the draft as
   independent evidence for offsets-not-parens).
3. Certificate-carrying runs: no analog anywhere in the survey,
   kernel or generic. KallGraph remains the silent-caps contrast.
4. Measured falsification catalog: no analog.
5. 1-bit VX provenance: no analog.

**Formulation claim — nearest neighbors now identified.** MoYe
(OOPSLA'25: client-driven graph reduction, exact for given
source-sink pairs), CAT (avoids unproductive summaries), FLARE
(index once, query many) all exploit client structure — but as
preprocessing/scheduling over the standard all-pairs relation. Ours
changes the relation computed (rooted F_G, origins as the only
stored facts, all icall queries sharing one propagation) and adds
semantic channel keys. Must-cite trio for the "client structure"
paragraph; the differentiator sentence stands.

**Precision side — the channel-key lever has NO competitor in the
survey.** Every precision entry is either a sensitivity knob
(LDCR/P³Ctx callsite contexts, MCFL stacks) or a type hybrid
(KallGraph, Li'23 hybrid — both already in our draft). Nobody keys
channels by the kernel's own registration identities. This is the
paper's clearest open ground, unchanged.

**Incremental positioning.** POPL'24 dynamic bidirected Dyck
(O(n·α(n)) updates incl. deletions) gets the same scoping treatment
as POPL'18: bidirected fragment only. Our composite grammar is not
bidirected; our incremental result (#43) is kernel-scale,
addition-only, FI-validated/fs-refused, gated by byte-identity —
different regime, cite side by side without implying either
subsumes the other. (Their deletion support could in principle
apply to our bidirected JOIN LAYER alone; our incremental blocker is
the fs residue, not the join layer — a footnote, not a lever.)

**Original three risk items, resolved as far as a survey can:**
- InterDyck/mutual-refinement line: moved to MCFL hierarchy
  (POPL'25, underapprox) — no collision, clean contrast.
- Kernel indirect-call 2023–26: KallGraph (S&P'25) confirmed as the
  latest; survey names no successor. Still verify no 2026 follow-up
  removes the caps before submission.
- Group-weighted Dyck for interior pointers: survey names nothing —
  supports novelty #2, but absence-of-evidence; keep the manual
  check on WPDS instantiations.

**Positioning discipline (unchanged from the claim review):** our
differentiator against ALL solver-line entries is the formulation
shift (rooted client-specific relation + semantic channel keys +
evidence-carrying runs), not solver speed; do not let a table imply
we out-solve dedicated CFL engines on their own benchmarks. If a
reviewer asks "why not SQUID/FastMatrixCFPQ as your engine": the
wall is closure OUTPUT size (Σ|C|² law), which an optimal engine
reaches faster but cannot lower — the same argument already made
for GraCFL/POCR, now extended to the 2026 crop.

## Reviewed 2026-08-13: Li, Zhang & Reps, PLDI'20 — graph simplification for InterDyck

*Fast Graph Simplification for Interleaved Dyck-Reachability.*
Preprocessing that deletes edges provably on no InterDyck-accepted
path, sound for any downstream over-approximating solver. Mechanics:
exact contributing-edge identification is undecidable (reduction from
InterDyck-reachability), so relax twice — bidirect the graph, then
per component-Dyck contract all foreign-labeled edges — and on the
bidirected projection Dyck reachability is an equivalence (Fast-Dyck,
Zhang PLDI'13, O(m log m) union-find). Anchor-node criterion: an
open-⟨k edge into v contributes iff v's union-find rep receives a
second ⟨k edge (the Fast-Dyck merge IS the matched-partner witness);
fail in any component language ⇒ delete; iterate to fixpoint.
Eval: 95 Android taint graphs (avg 147k edges — toy scale; their CFL
baseline times out >1K edges): ~26% edges deleted, 2.18x downstream
speedup, 57% memory, over-approx solvers return 64.9% of pairs.

Placement for us:
- **Rediscovery bucket**: bidirect + union-find Dyck collapse = our
  join layer's lineage (already cited); "prune what can't contribute,
  computed on a relaxation" = bidi-prune's family. Cite this as the
  simplify-then-solve preprocessing contract; anchor test = supply-
  side cousin of answer-relevant roots / sink-seal.
- **Positioning contrast**: they accept InterDyck and fight its
  undecidability; we declined the interleaving (summaries for
  context, Z_P quotient for fields = their "regularize one Dyck"
  baseline, but deliberate, container_of-sound, solved EXACTLY).
  Their precision gain exists only because their solvers
  over-approximate; for an exact decidable formulation,
  simplification buys time/memory, never answers.
- **Borrowable: FI-as-simplifier for fs runs.** FI is a sound
  quotient of fs-P (drop shifts: every fs derivation maps to an FI
  derivation over the same edges), so edges participating in no FI
  derivation of any icall answer are fs-dead. We hold the HEAD FI
  closure (3:30h) + witness-exact attribution; target = the 70h/365GB
  kernel fs run (same "recouped above 7s" economics, x1000 scale).
  OPEN before claiming: (a) measure delta over bidi-prune's cone
  intersection (closure-participation vs cone membership); (b)
  collision check vs Ding–Zhang mutual-refinement line (~2023, two
  abstractions pruning each other — closest published relative).
  Also queue: Kjelstrøm–Pavlogiannis POPL'22 (bidirected InterDyck
  decidability/complexity) for the formulation-contrast paragraph.

Local resource (2026-08-13): ZJU-PL **Lotus/Phoenix** checkout at
`/data/csong/opensource/lotus` carries reference code for both open
items — `lib/CFL/MutualRefinement/` (SAS'23) and
`lib/CFL/InterDyckGraphReduce/` (this PLDI'20 paper, matrix-based) —
plus `lib/Alias/Specialized/FPA/` with FLTA/MLTA/enhanced-MLTA/Kelp
reimplementations (USENIX Sec'24 lineage from the §5 diligence list)
and Canary DyckAA (AGPL; unification-only bidirected Dyck = natural
"join-layer-alone" ablation baseline). LLVM-14-only (typed-pointer
era): kernel baseline runs need a clang-14 5.18 corpus.

## Measurement/ablation catalog as a contribution (2026-07-24, user-flagged)

No existing CFL-reachability / kernel-callgraph paper reports the
kind of causal instrumentation this project now runs routinely:
merge-witness provenance (which origin keyed each unification),
witness over-determination (single-witness ablations are null —
ensembles glue hubs), residency-vs-causality (top hub residents
ablate to <0.5%), rule-class upper-bound probes (rodata-join skip
bounds a refinement at ~16% before building it), and the
identity-splitting funnel (five confirmable wrapper shapes, per-
feature conversion telemetry, and the negative: wrapper identity is
not the km hub driver). Four falsified sizing hypotheses in one
day, each from a <15-min probe. Position in the paper as the
measurement methodology section: sound-by-construction probes
(LEDGERed, answer-diffed) that attribute closure growth causally
BEFORE committing engineering effort — the counterpart to the
certificate-carrying-run story on the soundness side.

## The paper's spine: code semantics -> graph structure -> solving bottleneck (2026-07-24)

Existing work silos into algorithm (Dyck/CFL complexity, POPL'18),
graph processing (GraCFL/Graspan/POCR), or end results (callgraph
precision/soundness tables). None traces the causal chain from
SOURCE IDIOM through the GRAPH PATHOLOGY it induces to the SOLVER
SYMPTOM it causes — which is where both precision and scalability
are actually decided. Our catalog, every edge probe-established:

| code idiom | graph structure induced | solver bottleneck | evidence / fix layer |
|---|---|---|---|
| shared string literals, const ops tables | shared-witness ensemble joins | whole-object merges under FI; hub formation (closure size + precision) | witness provenance + rodata probe (bounded ~16% — ENSEMBLE, no single class causal); fix: field cells, not witness rules |
| alloc wrappers, kmemdup/dup family | shared ret-node identity + shared internal objects | cross-caller witness bridges; copy-loss soundness hole | summaries arc: -763 km / -1,659+5,802 kernel pairs; ALSO the negative: wrapper identity does NOT drive the km hub |
| circular list_head registration | cyclic witness dependence | demand-driven root minting INCOMPLETE (algorithm-level!) | lazy-mint kernel deficit -5,737 pairs; catch-up round; Lean necessity counterexample + F11 |
| type-erasing interpreters/rings (BPF regfile, GuC wq) | single identity spreading through connected webs | hub riding inflates witness counts (residency != causality) | ablations null at <0.5%; first-firer bias in provenance |
| kthread/work/timer void* payload channel | 92% of formals' hottest class = one hub | fs planes cannot discriminate across merged classes | fs13 == FI on hb; discrimination requires identity splitting BEFORE field sensitivity pays |
| container_of / intrusive structs | offset composition requirement (interleaved Dyck) | sound grammar scaffolding is V x (P+1): saturation OOMs; answer-anchored survives | shift-residue grammar; solver-side encoding |
| C++ struct-copy churn (memcpy) | residue-copy origins vs wildcard smear | fallback elimination is NOT free precision (net-negative fact volume) | --cfl-residue-copies measured negative on hb |
| kernel patching idioms (static_call, tracepoints) | shared-param conflation via tiny utilities | 600k+ phantom pairs through 3-line updaters | per-idiom primitives; the 'tiny utility' law |

The unifying law: closure cost and precision loss are both governed
by Sum(|a-connected component|^2) over the quotient, and the
quotient is shaped by IDENTITY CO-OCCURRENCE — which is a property
of source idioms, not of the solver. Papers that tune solvers or
grammars without this layer optimize the wrong variable; papers
that report precision tables without it cannot say WHY numbers
move. Our probes (witness provenance, no-mint ablation, rule-class
upper bounds, funnel telemetry) are the instruments that make the
middle layer measurable.

## KallGraph dossier (added 2026-08-07, ~/kallgraph.pdf + source audit)

Li, Sridharan & Qian, *Redefining Indirect Call Analysis with
KallGraph*, IEEE S&P 2025. UCR colleagues; open source at
github.com/seclab-ucr/KallGraph (audited checkout: /data/csong/
opensource/kallgraph, commit 058f9b5, 2026-02-04). This is the
current SOTA kernel indirect-call system and the paper our related
work must anchor against.

### What the paper is

1. **A demolition of the type-based line** (FSA -> MLTA -> TyPM /
   KELP / TFA / SMLTA): design-level unsoundness (type-confinement
   asymmetry; inclusion-only cast propagation) plus imprecision
   (FSA fallback on type escape / missing struct layers), inherited
   by every successor. Validated with fuzzing + ~150 person-hours of
   manual verification: MLTA has 100+ FN icalls / 1,703+ FN targets
   on defconfig Linux-6.5, 10x more on allyesconfig. **Cite this
   study as settling our motivation** — we no longer need to
   re-litigate why type-based resolution can't be trusted (the
   opaque-pointer erosion argument stays ours).
2. **A hybrid demand-driven design**: per-address-taken-function
   on-demand Andersen-style DFS over the SVF PAG (Unias lineage),
   with (a) byte-offset stack (MHS) instead of paired Gep matching —
   handles container_of-style interior pointers and (X+Y,-Z)
   arithmetic; (b) object-level CastMap (per cast instruction, not
   per type); (c) type-based shortcut edges (Unias) to skip long
   propagation chains; (d) bootstrapped on-the-fly fixpoint (no MLTA
   seed; ~4 rounds with dependency tracking DepiCalls/DepFuncs);
   (e) embarrassing parallelism (80 threads, read-only PAG).
3. **Headline numbers**: Linux-6.5 defconfig 10,539 icalls, avg 5.8
   targets/icall, 8h07m CPU (8m52s wall/80T); allyesconfig 80,484
   icalls, avg 17.5, 270 CPU-hours (3h49m wall), 246 GB RAM. 75-90%
   target reduction vs MLTA. FN validation: 7-day Syzkaller trace
   (937 icalls covered = **8.9% of icalls**) found 0 KallGraph FNs;
   manual sampling found 2 icalls / 9 FN targets, attributed to SVF
   PAG not modeling ptrtoint/inttoptr (integer-carried pointers).

### The undisclosed resource heuristics (verified in code)

The paper presents Algorithm 1 as a sound on-demand traversal and
claims soundness modulo the integer-channel caveat. The released
implementation adds THREE hard resource caps, none mentioned in the
paper (user's report from colleagues confirmed in source):

1. **DFS path-length cap = 35 edges**: `Prop()` silently returns
   when the current path exceeds 35 PAG edges
   (src/lib/KallGraphAlgo.cpp:35). Any alias path longer than 35
   edges (deep copy chains, multi-hop registration relays) is
   dropped — no counter, no log.
2. **Dynamic hub blacklisting**: past depth 15, node visit
   frequencies are tallied; every 20,000 deep visits the 50
   most-visited nodes are PERMANENTLY added to `BlockedNodes`, and
   `Prop()` refuses to traverse them thereafter
   (KallGraphAlgo.cpp:59-81, 32-34). The blacklist persists across
   queries — later queries inherit truncations triggered by earlier
   ones (result even depends on query order).
3. **Static popular-callee blocking**: formals of any function with
   more than baseNum*5 = 250 call edges per argument are blocked
   up front (src/lib/Util.cpp:107-115; baseNum=50 for both defconfig
   and allyesconfig, src/include/Util.hpp:4-6, KallGraph.cpp:461).
   This excises exactly the tiny-utility shared-param channel
   (sort comparators, __static_call_update-class helpers) that our
   measurements showed carries BOTH the kernel's worst conflation
   AND real fptr flow.
4. Lesser: type shortcuts gated at fan-out < baseNum^2 = 2,500;
   allocator call/ret edges skipped by substring match on
   kmalloc/kzalloc/kcalloc (KallGraphAlgo.cpp:53-57, 263, 289).

### Why this matters for positioning (the thesis writes itself)

Caps 1-3 are not arbitrary engineering warts — they are the
demand-driven signature of OUR wall. The traversal drowns exactly
where the may-alias quotient concentrates (the type-erased hub that
carries 93% of our resolved pairs; the >250-caller utilities; paths
through the giant component longer than any fixed budget). Their
fix is to cap the traversal at those points; the caps fire
precisely where the flows that are hardest to resolve live, so they
buy tractability by silently truncating the hub — which also
flatters precision (blocked hubs cannot contribute large target
sets). Their empirical FN validation cannot bound what the caps
cut: fuzz coverage was 8.9% of icalls, biased toward shallow
easily-reached dispatch, and manual verification sampled icalls
where KallGraph already reported targets. "Small target set" is not
"precise" without a soundness certificate.

Our contrapositive, point by point:
- They block the hub; we keep it, explain its formation (anatomy,
  C3), and drain it by certified constructions — identity channels
  at answer level with -N/+0 certification and completeness
  counters that must read zero (C2), surgical residues (C4).
- Their exactness debt is paid in per-query resource caps
  (unquantified FNs); ours is paid up front in the formulation
  (answer-anchored fact space) with the exactness of every
  subsequent transformation machine-checked (Lean) or
  run-certified (closure certificates C0-C5). No silent fallback
  is a project invariant enforced by assertion.
- Whole-program economics: their cost = (address-taken functions x
  per-query traversal x fixpoint rounds), absorbed by 80 threads
  and 246 GB; ours = one monotone solve whose fact mass is bounded
  by answer-relevant origins, on a desktop. Same wall, opposite
  ledgers.
- Their 2 admitted FNs are the integer channel (SVF PAG has no
  int-carried-pointer edges); we model 47,676 kernel int-provenance
  sites with witnesses and LEDGER the declines. They do not model
  inline asm (129,812 kernel sites, 13.7% ptr-capable), PREL32
  linker section arrays (initcalls are module-level asm, invisible
  in the PAG), or static_call/tracepoint patching families — each a
  modeled-or-ledgered boundary for us.

### Technical kinship to acknowledge honestly

- **Their MHS byte-offset stack and our Z_P shift residues are dual
  solutions to the same discovery**: Java-style exact Dyck field
  parens cannot express C interior pointers (their §5.3
  counterexamples = our t_container bug of 2026-07-07). Theirs is
  per-path state, affordable only inside a DFS; ours is the
  whole-program summarizable form (weight-domain quotient). Cite
  them as independent evidence that C field sensitivity does not
  belong in the parenthesis alphabet.
- Their on-the-fly bootstrapped fixpoint (no unsound MLTA seed) =
  the same wiring-feedback fixpoint we integrate; their dependency
  re-analysis (DepiCalls/DepFuncs) is the demand-side analog of our
  incremental re-solve.
- Their CastMap look-ahead (store only casts whose surroundings
  have real dataflow) rhymes with our census->confirm->adopt
  discipline, minus the completeness accounting.
- Their observation that MLTA was "an ad-hoc hybrid pointer
  analysis all along" (§5.2) is a genuinely good framing; our
  spectrum picture (type-based end / CFL end / demand-driven
  escape hatch) subsumes it.

### Claims discipline for the paper

- Attribute caps to "the released implementation (commit 058f9b5)",
  with file:line, not to the paper's algorithm — the paper is
  silent, which is itself the point (contrast with our
  certificate/ledger methodology, not a gotcha).
- Do NOT compare avg-targets-per-icall head-to-head as a precision
  claim in our favor or theirs (different kernel versions/configs/
  optimization levels, and their number embeds cap truncation);
  compare soundness POSTURE and cost model instead. If we run a
  head-to-head, run their released binary on our corpus and diff
  answer sets both directions with the caps instrumented.
- Their study's FN tables (Table 6) are a useful external ground
  set: candidate differential targets for our kernel runs
  (sys_call_table, rtnl doit, kprobes opt_pre_handler already in
  our task log).

## Research question (added 2026-07-31, from the task #31 blob verdict):
## provable control-plane stratum separation for a monolithic kernel

The blob-formation diagnostic showed the giant class is the exact
field-insensitivity quotient centered on the mm/phys stratum — code
one level BELOW the heap abstraction that user-space analyses hide
behind malloc summaries and syscalls. For the kernel that stratum is
analyzed code, and it re-enters the typed-object universe through
phys<->virt conversion channels (inlined __va/page_address = inttoptr
+ direct-map arithmetic, i.e. the int-provenance layer).

QUESTION: can we PROVE, for Linux, separation of the control plane —
that no flow from (a) user-space-controlled memory or (b) raw data
payloads (pages, packet buffers, trace payloads) reaches indirect-call
resolution, except through an enumerated, reviewed crossing set
(allocator interfaces)?

Method (the project's standing discipline, lifted to a theorem):
partition origins into strata (typed kernel heap = FRESH origins;
kernel globals; phys/page stratum via int-provenance witnesses
(PAGE_OFFSET / vmemmap arithmetic, pte channels); user-boundary
interfaces (copy_from_user targets, user-mapped rings); payload
buffers) and CHECK on the sound closure that stratum crossings into
fptr cones are empty modulo the reviewed set. Every violation is a
finding: imprecision (hub smear -> refinement ladder), a benign
design fact needing a certificate (io_uring: shared pages but
opcode-INDEXED dispatch, never user-supplied fptrs), or a real
user-data-to-control channel (a security result per se).

Positioning: noninterference proofs exist for microkernels (seL4) by
construction; kernel CFI deployments ASSUME this separation without
evidence; type-based kernel callgraphs (MLTA/TypeDive) cannot even
express it. Derived separation certificates with an auditable
exception list for a monolithic kernel would be a standalone
contribution, and the precision arc (tasks #28-#31: pair channels,
soundness fixes, sink channels, stratum boundary) is exactly the
machinery that makes the theorem checkable: provability and precision
are the same ladder. First empirical test = the stratum-ablate probe:
if separation holds on the corpus, segregating phys/user strata
removes ~0 true pairs while fragmenting the 73k-member quotient class.
