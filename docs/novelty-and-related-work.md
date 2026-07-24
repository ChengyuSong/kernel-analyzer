# Novelty ledger and related-work positioning (2026-07-18)

Honest classification of the flows-to (ORCFL) work: what we
rediscovered from the literature, what instantiates known frameworks,
and what we can defend as novel. Written after reading Chatterjee,
Choudhary & Pavlogiannis, *Optimal Dyck Reachability for
Data-Dependence and Alias Analysis*, POPL 2018 (popl18b.pdf in repo
root) against our results log (cfl-graph-explosion-and-scaling.md).

Caveat: literature knowledge is as of early 2026 and was NOT verified
by a fresh search; see "Diligence before drafting" at the end.

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

## 5. Diligence before drafting related work

Highest collision risk, to be checked manually (web search
unavailable from the analysis environment):
- 2024–26 InterDyck / mutual-refinement solver lines (Ding, Zhang
  et al.) — interaction of two Dyck languages vs our
  valley-grammar + weight split;
- recent kernel indirect-call work (Kelp/TFA/Unias lineage,
  2023–25) — whether anyone couples CFL-based flow with kernel-scale
  soundness claims;
- group-/lattice-weighted Dyck reachability for C field sensitivity
  (WPDS instantiations) — whether the Z_P quotient has been used for
  interior pointers before.

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
