# Lean vs Implementation Gaps

This file tracks the major gaps between the Lean formal model in `proof/lean`
and the current C++ implementation in `src/lib/CallGraph.cc`.

Cross-links:
- Implementation doc section:
  [`docs/compositional-cfl-analysis.md`](../../docs/compositional-cfl-analysis.md)
  under "Current mechanization gaps (Lean model vs implementation)"
- Lean overview: [`README.md`](README.md)

## Major gaps

1. Obligations are assumed, not discharged from implementation code.
- Lean proves soundness once graph-homomorphism obligations are provided.
- We do not yet prove that `compressConstraintGraph` + `runCompositionalSolve`
  construct those obligations for all inputs.

2. Iteration model mismatch.
- Lean models unbounded fixed-point closure (`iterClosure`).
- Implementation uses explicit caps:
  - per-TU: `kMaxPerTUIterations = 32`
  - composed/global: `kMaxCompIterations = 8`
- With finite monotone edge growth, convergence is guaranteed without caps, so
  caps are defensive and can stop before the true fixed point.

3. Compression model mismatch.
- Lean quotient/composition is abstract edge remapping.
- Implementation drops SCC self-loops during remap and then re-adds terminal
  `a/-a/d/-d` loops for multi-node SCCs.
- A proof that this concrete construction refines the abstract model is pending.

4. Boundary completeness is assumed in Lean.
- Lean assumes all cross-TU-relevant boundary facts are exported.
- The Lean kind set now includes implementation-required classes
  (`func/arg/ret/vararg/glob/icall/larg/lret/lvararg/icallarg/icallret`),
  but export completeness is still an assumption.
- Lean now models boundary-node pinning (`pinBoundaryNodes`) and proves
  soundness preservation under seed self-edge addition, matching the
  edge-isolated-boundary fix direction in implementation.
- Implementation depends on extraction paths (metadata and pattern-based
  discovery), plus cache sanity checks.
- Completeness of these extraction paths is not formally proved.

5. Summary bridge discovery is abstract in Lean.
- Lean models assign-pair summary generation (`assignBridgeRule`) from an
  abstract monotone bridge relation.
- Implementation computes concrete bridges from resolved indirect-call targets,
  `icallarg` symbols, and callee arg/vararg symbols.
- A refinement proof connecting implementation bridge extraction to the Lean
  bridge predicate is pending.

6. Target filters are not yet formalized.
- Implementation applies `isCompatible` and field-store filtering
  (`fieldFilterAccepts`).
- Lean currently has no model/proof that these filters are conservative with
  respect to monolithic truth.

7. Allocator promotion logic is out of model.
- `findCustomAllocators` and `findCustomAllocatorsComposed` mutate allocator
  sets and may rewrite call-related edges in monolithic mode.
- Lean does not model this state transition or prove its preservation properties.

8. Solver implementation is trusted.
- Lean reasons over declarative reachability.
- `SolverFWGramParallel` is treated as an oracle in the end-to-end story.
- A refinement proof (solver output implies declarative `Reach`) is missing.

9. Function-identity canonicalization is not modeled.
- Implementation uses GUID-based identity in places where pointer identity can
  diverge across declaration/definition forms (e.g., compositional func-node
  collection and field-store correlation).
- Lean currently abstracts over node/function identity and does not model this
  declaration-vs-definition canonicalization step.

## Notes

These gaps do not invalidate the current Lean schema proofs. They define the
work needed to claim a full machine-checked proof for the exact production
pipeline.

---

# Flows-to (ORCFL) model gaps — added 2026-07-14

The primary solver is now `runFlowsToResolution` (branch `orcfl`), modeled in
`CompositionalCFL/FlowsTo.lean`. Machine-checked so far:

- `fderiv_mono`: derivability monotone under edge growth — covers the outer
  fixpoint (resolve icalls → `handleCall` wiring → re-solve only adds edges).
- `fderiv_map` / `fderiv_quotient`: derivability preserved under node
  quotients — covers presolve copy/field merges, cell-cluster union-find
  merges, and the dynamic a-SCC collapse (soundness direction).
- `solver_complete`: given the closure rules and the `origins_minted` hypothesis
  (origin ⊆ minted), the solver derives every
  grammar-derivable flow and alias.
- `answers_complete`: icall answers (shift zero or ⊤ at the fptr) are found
  whenever function nodes are minted and `origins_minted` holds.
- `sderiv_catchup` / `catchup_answers_complete`: staged (lazy-mint)
  solving with a final catch-up to full minting equals the from-scratch
  closure — exactness of task #21's catch-up round.
- `answer_not_derivable_restricted`: restricted minting genuinely loses
  answers (counterexample), so `origins_minted` cannot be weakened
  without a sufficiency proof for the restricted set (open, F11).

## Flows-to gaps

F1. [REVISED 2026-07-14] The grammar is now ROOTED at origins
(`FDeriv`'s `origin` parameter), and the solver hypothesis is
`origins_minted : origin ⊆ minted` — dischargeable, since the
implementation mints every origin-bearing class. The July-13 minting
bug is a violation of exactly this hypothesis. Remaining code-level
gap: the correspondence between Lean origins and the implemented
criterion (canonicalClassMembers sweep over alloca / global /
alloc-site values) is informal. Note the rooting DEFINES a semantic
difference from pairwise saturation: saturation admits unrooted valley
apexes (φ-cycles, entry-less store/load loops = undef values), so
flows-to ⊆ saturation on such patterns is principled, not a bug —
exact saturation parity is the wrong validation target.

F2. a-SCC collapse precision-neutrality (the converse of `fderiv_quotient`)
is unproved. Soundness needs only the proved direction; the claim that
collapsing mutually shift-preserving-reachable classes loses no precision
rests on the cycle-insertion argument, checked only empirically
(identical per-icall results on libpng/harfbuzz).

F3. [DOWNGRADED 2026-07-14] Union-find cluster transitivity was
suspected to over-approximate the grammar's per-witness M; writing the
model shows it is FACT-EQUIVALENT: `flow_m` steps chain across aliased
cells, so fact sets equalize transitively in the grammar too — the
solver never consumes the alias judgment itself, only the fact flow.
Residual: cluster merges also unify cell lists and edges of the merged
content classes; believed equivalent by the same chaining argument at
each pointer level, not formally checked. `ClusterTrans` runtime stats
(keys/cluster, transitive key-coalescing merges) monitor the coarsening
empirically (libpng FI: 506/546 keys in one cluster, resolution still
exactly matches saturation).

F4. VX bridge provenance (bridged facts never cross a second bridge) is
abstracted away: the model's `⊤` joins are unrestricted, i.e. at least as
permissive as the implementation. Completeness of the 1-bit provenance
restriction w.r.t. the grammar's value-step-laundering is checked only
empirically (phase-2 null result).

F5. The shift monoid instance proved is exact `Nat` offsets; the production
`Z_P` residue bucketing is a monoid quotient of it (sound abstraction),
but the quotient homomorphism is not yet formalized (needs `Fin P`
arithmetic or mathlib).

F6. `FactSet` (hybrid sparse/dense planes) is trusted as a set
implementation; no refinement proof.

F7. Iteration cap `--cfl-flows-to-max-iters` can stop before the outer
fixpoint; the implementation warns ([UNSOUND-RISK]) when it triggers.
Model assumes full closure.

F10. [ADDED 2026-07-14] The SolverModel closure fields (seed/step_a/
step_f/step_fx/step_mal) assume the worklist algorithm reaches
saturation — the delta/backlog machinery (jdirty refill on merge,
joined-plane intersection, merge-abort requeue) is where historical
solver bugs lived and is below the model. Practical discharge:
`--cfl-verify-closure` runs one full non-delta scan post-fixpoint and
asserts no rule fires (C0 backlogs drained, C1 a-prop, C2 f-prop,
C3 wildcard projection, C4 fact x cell joins, C5 bridge crossings) —
a per-run certificate of the model's assumption.

F11. [ADDED 2026-07-23, task #21] Lazy minting. Machine-checked:
`SDeriv` (least staged closure with a `base` fact relation),
`sderiv_catchup` (staging confluence: restricted drain → mint more →
continue = from-scratch closure over the final root set — the
exactness of the catch-up round, commit 446f35b),
`catchup_answers_complete` (end-to-end: staged solve with final
minting ⊇ origins finds every accepted answer), and
`answer_not_derivable_restricted` (necessity: a 5-node graph where
minting a strict subset of origins loses a grammar-derivable answer —
the July-23 whole-kernel deficit, -5737 pairs through tcp_ulp/9p ops
registration lists, is this shape at scale). OPEN: characterizing a
SUFFICIENT restricted root set. The implemented A-closure
(backward {a,f} + cell→owner hops on the live quotient, recomputed
per drain fixpoint) was conjectured sufficient by the first-missed-
join induction (scaling doc §2026-07-18) and is empirically REFUTED
at kernel scale — the induction breaks when a witness's consequence
path and another witness's occurrence path each need the other's
merge (cyclic dependence through circular list structure). The
catch-up round makes the conjecture moot for exactness; a formal
minimal-sufficient-set characterization would recover the ~3x
fact-mass savings without the catch-up's final-round cost.

F8. Target filters (`isCompatible`, `fieldFilterAccepts`) still unmodeled
(same as compositional gap 6): they subtract from the sound answer set,
so each rejection is a potential soundness hole. The planned
completeness-bit for `fieldFilterAccepts` and per-filter rejection
counters are prerequisites for retiring them; formalizing "filters reject
only grammar-underivable pairs" would discharge the gap.

F9. Edge-encoding completeness (IR construct coverage) is out of scope of
the model entirely: the July 2026 aggregate call-boundary bug lived here.
The systematic IR-construct census (task #13) is the practical mitigation.

## Batched solving (tasks #40-#42, added 2026-08-06)

Covered by the model (`WDeriv` section in `FlowsTo.lean`):
- `batched_exact`: sound + closed witness table ⇒ union of per-batch
  closures = eager closure (the #40/#41 exactness argument).
- `wderiv_restore`: spill restore-and-continue under a grown table equals
  the fresh drain (the #42 exactness argument).
- `wderiv_sound` is the per-round invariant that keeps the accumulated
  table sound from the empty start.

NOT covered (implementation-level, below the model's abstraction):
- The union-find/clusterRep/bridge machinery is modeled as the witness
  TABLE; that the recorded events regenerate exactly the join topology
  (worker replay, VX bridging) is unverified.
- The touch-window re-offer discipline (per-batch cursors, hot-class
  full re-offer, quiescent joined:=R∪RB) computes the `wderiv_restore`
  closure — the delta-completeness of that discipline is unverified.
- Batch-local universes (rid-blo bit translation) are a data-layout
  bijection, unverified.
- Round termination (monotone merges) is argued informally; the model
  takes the stable table as a hypothesis rather than constructing it.

## Review-response additions (2026-08-11, docs/proof-review.md)

New machine-checked results (all in `FlowsTo.lean`, build clean on
lean4 stable/4.33.0, no sorry):

- `sderiv_sound_fderiv` + `sderiv_iff_fderiv`: the CONVERSE of
  `solver_complete` for the least closure — least-closure/grammar
  equivalence at exact seeds. Replaces the informal "fact-equivalent"
  claim; F2 (a-SCC converse) and the extra-implementation-roots
  widening remain open above the least closure.
- `pol_solver_complete` + `pol_answers_complete`: per-root seed
  POLICY (exact vs widened) — resolves proof-review finding #1: the
  surgical wildcard mint now has its abstraction theorem (widened
  origins' answers surface at ⊤, which acceptance includes).
- `ShiftHom` / `fderiv_shift_hom` + `intShifts`/`zpShifts`/`natToZp`:
  residue abstraction is a proved homomorphism transfer; partially
  discharges F5. REMAINING: the signed instance intShifts → zpShifts
  (the implementation's ((o % P) + P) % P normalization).
- `Core.lean` `boundary_sound` fixed to same-PRESENT-symbol (the old
  `symbol x = symbol y` form also related none = none).

Certificate/code movements the model should eventually absorb:

- C6 (seed presence per mint policy) and C7 (mint coverage at the
  final quotient) added to --cfl-verify-closure: the SolverModel
  hypotheses `seed` and `origins_minted` are now checked per run,
  not assumed (proof-review finding #4).
- F7 RESOLVED at the policy level: iteration-cap exhaustion now
  REFUSES to emit answers (exit 1) unless --cfl-iter-cap-ok.
- Batch stop condition strengthened to full retained-witness
  stability (merges + mints + cluster keys), syntactically matching
  `batched_exact`'s hclosed. OPEN (F12): the lemma that the weaker
  merges-only condition already suffices — a single-member key
  insert is alias-inert (joins need two co-clustered cells) and
  self-batch-closed (facts carry their own origin, so only the
  inserting batch can add the second member, and it just closed) —
  is argued in a code comment, not yet in Lean.
- OPEN (F13): formal `ReportedAnswer` semantics (identity channels,
  transfer summaries, post-filters, fallback cases) — the
  proof-review's repair #5; channel soundness currently rides on
  per-family completeness contracts and the regfield closedness
  certificate.

## Origin bundles (Bundles.lean, 2026-08-15; implementation REMOVED 2026-09-04)

The v1 implementation was removed under the fix-or-remove policy
(Gate 2 wall fail; docs/origin-bundles-design.md). The theorems
below stay as the specification for any future attempt — same
policy as Incr.incr_exact.

Machine-checked: `bundle_exact` (quotient of closure-row-equal
origins, bundled closure = per-origin closure member-by-member;
mixed-witness joins collapse via row equality), `row_determined`
(equal carried-base rows containing own seeds ⇒ equal closure rows —
the drain-checkpoint full-state hash test justifies the RowEq
hypothesis). Unverified engineering (v1 implementation gates):
- rid renumbering pass = bijection on plane bits (runtime count
  assertions);
- cluster-key remap + L1 equal-or-absent assertion (coupling through
  shared cells is BELOW the model, like event-replay order);
- harvest/dump expansion of bundle bits to leaves;
- exclusion completeness: prot rids and measurement-flag rids are
  the only per-rid mechanisms post-seeding (audited 2026-08-15;
  re-audit on any new addFact call site).

## Channels.lean (2026-08-25, answer-level levers)

- `clamp_sound` (regfield): both hypotheses are ASSUMED from the
  implementation side — `Closed` maps to the hazard-counter
  certificate (unwitnessed stores/atomics/bulk copies/escapes refuse
  the key), `attr` (clamped sites read the key) rests on the
  GEP-derived site key, a structural surrogate the code does NOT
  certify. `clamp_needs_attribution` is the machine-checked
  counterexample for dropping `attr` — the reason the object-
  population re-founding (docs/rendezvous-keying-design.md) exists.
- `objclamp_sound`: the re-founding's safety argument — the site
  obligation weakens to slot-agnostic object membership; slot
  misattribution becomes harmless by construction. The implementation
  does NOT yet aggregate populations this way (v2 item).
- `nulljoin_sound`: `null_unrealizable` encodes store-through-null UB;
  the guard ships (fires 0x on current corpora).
- `skipwiring_sound`: `cert` (transferFree callees introduce no flow)
  is the HAND AUDIT of the EMPTY/NOOP entries in func_summaries.txt —
  per-entry English arguments, not discharged from IR.

## 2026-08-29 campaign close

- Channels.lean gains `stride_union_sound` + `element0_unsound` (the
  machine-checked form of the GT 79->90 regression: an unknown array
  selector demands the union over the residue class, mirroring
  `clamp_needs_attribution` for site keys) and the interior-member
  note (row 5 = stride union composed with an offset shift).
- NEW ASSUMPTION recorded: rodata channels treat a constant global's
  initializer as its runtime content (kernel rodata immutability /
  W^X). Not discharged from the corpus.
- RETIRED: the witness-taint population-closure obligation (the pass
  was retired by design review — same-computation redundancy; see the
  rendezvous design doc tombstone). No Lean debt remains for it.
- The clamp/objclamp/nulljoin/skipwiring schemas correspond to the
  FINAL shipped mechanism set (row-5 pins = the empirical fixed point
  of the semantic-key index; research log tasks #56-#62).

## Modeling policy + backfill ledger (2026-09-04, user directive)

POLICY: every optimization ships with a corresponding model-level
statement of its exactness/soundness, with assumptions explicit.
Byte-identity gates check executions; the theorem is the reference
the implementation is checked AGAINST. Gates alone are a point
check and do not license enablement outside their gated envelope
(the incremental-518 lesson).

Inventory audit:

MODELED (statement + proof, no sorry):
- cell quotient / witness joins ....... sderiv_iff_fderiv (2-sided)
- node quotients (presolve, a-SCC) .... fderiv_quotient (sound;
                                        precision-converse open)
- Z_P offset abstraction .............. fderiv_shift_hom
- selective wildcard seeding .......... pol_answers_complete
- lazy minting + catch-up ............. sderiv_catchup (+ 7-node
                                        counterexample for no-catchup)
- batched solving ..................... batched_exact / wderiv_sound
- spill restore ....................... wderiv_restore
- origin bundles (impl removed) ....... bundle_exact / row_determined
- channel mechanisms .................. Channels.lean (clamp/objclamp/
                                        nulljoin/skipwiring/stride +
                                        counterexamples)

GATE-ONLY (backfill required; priority = silent-completeness risk):
1. [THEOREM DONE 2026-09-04, Staging.lean::Incr.incr_exact]
   incremental cross-iteration. Two-sided equivalence of the
   fresh-triggered (delta-worklist) closure with from-scratch,
   under `delta_seeds_complete`: every NEW instance (R' \ Rn)
   with ALL-OLD premises must be seeded — instances with a fresh
   premise self-fire; old instances already fired into Fn. The
   518 miss is exactly this clause (new call edges joining old
   actual-facts to old formal-cells). IMPL REPAIR STILL OPEN and
   still blocks re-enablement: the seed enumeration must cover
   R' \ Rn instance kinds with all-old premises. CERTIFICATE
   VALIDATED 2026-09-04: opt-in incremental + --cfl-verify-closure
   at 518 -> 5,101 violations, assertion abort (the per-run check
   detects the hypothesis violation in ONE run).
2. [DONE 2026-09-04, Staging.lean] bidi-prune at FI ...
   `prune_sound`: cone-miss origins appear in no answer; hypotheses
   = ans_at_dispatch + cone_covers-FOR-THE-CURRENT-GRAPH (the #43
   re-admission obligation, now a named hypothesis).
3. [DONE 2026-09-04, Staging.lean] adoption ... `adopt_sound`:
   soundness (not exactness) under atoms_complete = the proposer's
   completeness contract. Correctly reclassified as a precision
   mechanism.
4. COW plane sharing (#46) ............ detach-on-divergence
   exactness: shared plane mutation-isolation as bisimulation of
   unshared planes. Data-layout-adjacent; medium risk. OPEN.
5. [DONE 2026-09-04, Staging.lean] join fast path ...
   `mark_skip_exact`: conservative marks (mark_sound) + join
   idempotence (member_noop) => skipping loses no effect;
   one-directional by construction.
6. [DONE 2026-09-04, Staging.lean] presolve-once ... `memo_exact`:
   trivial theorem, load-bearing hypothesis (`unchanged` is what a
   stale spill dir violates).
ASSUMPTION-CLASS (bijections; theorem not required, assumption
stated): fused kernels, BitPlane layout, batch-local universes
(rid-blo translation), GUID interning.

## Presolve V-components without GraCFL (2026-10-02, plan-named-cells A.1)

The default presolve (cone hybrid) quotients the memory-free a/f
sublanguage by the connected components of V. Until 2026-10-02 V was
materialized by a GraCFL closure of that sublanguage; it is now
computed by `ka::valleyComponents` (src/lib/SCC.h).

STATEMENT (prose, not mechanized). Over exact edges u ->_r v (a: r=0,
f<b>: r=b mod P; fx edges excluded, as no V rule consumes them),
  x V y  iff  exists z, s. z ~>_s x and z ~>_s y.
Let ROOT be the SCCs of the edge graph that no edge enters from
another SCC, and pick any member w_R of each. Then
  components(V) = components of the union over R of
                  { {x : w_R ~>_s x} : s in Z_P }.
Proof: (<=) each group is a set of nodes sharing the token (w_R, s).
(=>) if x, y share the token (z, s), some root member w reaches z
with shift d (follow predecessors to a source SCC; inside an SCC
every member reaches every other), so x and y share (w, s + d).
Representative choice and component numbering do not matter: the
presolve merges each component into its first member in local-id
order, as before.
GATE: cross-checked against the GraCFL closure (partition identity,
no mismatch) on libpng FI/P=13/P=16/all+ids/cone-off, nm-new O0
FI/P=13/all+ids, cflow O3 FI/P=13/all+ids, km FI full; answers
byte-identical on the consumer gate (test/consumer-gate.sh).
BACKLOG: mechanize as `valley_components_exact` next to
fderiv_quotient.

## Named cells (NamedCells.lean, 2026-10-02, plan-named-cells B.3)

Statements (checked, standard axioms only):
- `named_sound_fderiv`: every named derivation, for any admissibility,
  is an FDeriv derivation on the erased graph (named planes are
  removal-only against the current specification; gate G2).
- `named_sub`, `nderiv_adm_mono`, `uncertified_read_eq_today`: a
  stricter policy derives less; with no certified name, named = today.
- `named_read_sound`: against the exact-offset reference semantics
  (`CDeriv`: a store and a load meet iff their pointers carry the same
  object and offset; `fx` moves to an arbitrary offset), named
  derivations cover every concrete value flow, given `CertConsistent`.
- `merge_keeps_names`, `read_merge`, `read_noleak`
  (merge_lossless_named): planes merge name by name; a certified read
  of a merged class never returns content filed under a non-alias name.
- `nbatched_exact` (batched_named_eq): `batched_exact` with
  name-indexed cell planes.

Semantics fixed by the model (and a correction to the plan): only a
load through a CERTIFIED name filters; it reads the planes of the
layout aliases of its name and NOT the unnamed plane. An uncertified
named load reads every plane, as today (plan 3.2 item 4 would have let
it skip other names' planes, unsound under type punning).

Implementation obligations left open:
1. Fidelity of the graph: the implementation's store name is the
   access name (deepKey) of the store's address expression; every
   other write into a cell (memcpy cell-to-cell copies, summary atoms,
   initializers, asm closures, channel wiring) is a store with name
   `none`; every other read of a cell (cell content used as a pointer,
   copies out of cells) is an unnamed load. Checked by construction in
   code review, not mechanized.
2. `CertConsistent` is a hypothesis about the program. The certificate
   census (plan 3.4: no escaped field address, no bulk copy from a
   non-constant source, no atomic with a non-constant value, no
   variable offset reaching the field, no copy-in from an open name,
   bare-pointer stores open every name they could cover) is its
   intended syntactic discharge; the census's completeness against
   `CertConsistent` is argued in docs, not mechanized.
3. `lalias` completeness: the layout-alias table (nested structs at
   the same offset, unions; a name inside a union is open) must
   contain every pair of names that can denote the same concrete cell.
4. The reference semantics' soundness for machine executions (the
   standard inclusion-based argument) is assumed, as for FDeriv.
5. Spill/restore (`wderiv_restore`) and staged minting
   (`sderiv_catchup`) are not restated for named planes; their proofs
   do not inspect cell contents and should transfer, unchecked.

### The shadow-cell realization (`--cfl-named-planes`, WIP 2026-10-02)

What the solver runs (docs/named-cells-design.md): every write that is
not filed under a name goes to the cell's unnamed shadow; a named load
reads its name's shadow and, unless its name is certified, the unnamed
shadow. Statements (checked, `propext` only):
- `realize_sound`: against `RDeriv` (`CDeriv` plus identities: an
  origin cell is unnamed content of every concrete cell its pointer
  reaches), every concrete flow is a `KDeriv` flow of the realized graph
  — `FDeriv` plus `mal_sat` (aliased cells alias their shadows of each
  name: the solver keeps shadows as satellites of their cell's class and
  merges them name by name when classes merge) and the identity seeded
  into the shadows — given `Realizes` (the graph construction),
  `PunFree` (a named store and a named load of one concrete cell use
  the same name) and `CertNamed` (content filed under no name never
  reaches a load of a certified name). Identities (`RDeriv.cid`) are
  content under every name, matching their seeding into every shadow.
- `realize_removal_only`: projecting shadows onto their cells maps
  every `KDeriv` derivation onto today's `FDeriv` on the erased graph,
  given that the realized graph has no other edges.

Obligations left open:
6. `Realizes` is checked by construction: every write into a raw cell
   passes `addAssignmentEdge` (or `initSlotWrite`) and is filed or
   mirrored there; every cell gets an unnamed shadow before each solve
   (`ensureUnnamedShadows`); a root minted on a class is seeded into
   the unnamed shadows of the class's raw cells. That the solver's
   satellite merges realize `mal_sat` (every class merge, cluster join
   or a-SCC collapse, merges the satellites of each name) and that the
   relevance oracles see a shadow as part of its cell (`--cfl-bidi-prune`
   unites them; slicing and lazy minting are refused) is not mechanized.
7. `PunFree` is a program assumption (type data in the answer path).
   Exposed partially: chains that cast a position to a struct the
   layout lacks, bases indexed as two unrelated structs, and unions are
   unnamed; casts across functions (`void *`) are not detected.
10. `CertNamed` is discharged for typed writers by construction (a
   write whose pointer has a struct position is filed under its leaf,
   or opens every leaf of the structs it may lie in) and ASSUMED for
   untyped writers (no struct position): under
   `--cfl-named-untyped=count` they are counted per run ("blind spot",
   with the writing functions); `open` certifies nothing. Summary atoms
   are positioned by the summarized function's formal (debug-info type,
   else the one struct its body indexes it as); a wrong formal type is
   a `PunFree` violation. A write into a union field opens only the
   structs the chain enters inside the union (a union has no names of
   its own); a union write with none inside is counted as untyped.
   Precision-only (no obligation): the presolve cone crosses names, so
   values stored under a name read at an icall stay out of V-merges.
8. Name-preserving copies (cell-to-cell copies relay each name's
   shadow to the same name's) extend `PunFree` to copied content; the
   relayed names are discovered from the solution and wired in further
   outer iterations (monotone), not mechanized.
9a. Name sources: GEP chains, declared types of globals and stack
   slots, struct-path TBAA tags, debug-info types of formals and
   dbg.value-described pointers (through casts; anonymous structs by
   typedef; structs only debug info describes, by their members). All
   are the program's declaration of what the memory is; `PunFree` is
   that they hold at run time. A pointer vector access is filed under /
   reads every lane's name.
9. Names are canonical leaf names, so `lalias` is equality; struct
   names are unified across modules by stripping numeric suffixes (two
   different layouts with one tag share names: coarser, still sound).

## Type labels (TypeLabels.lean, 2026-10-03, plan-named-cells 3.9)

Statements (checked, `propext` only):
- `label_sound`: against `RDeriv`, the exact semantics over concrete
  instances `(site, label)`, every concrete flow is covered by
  `LDeriv` through the instance's plain origin or its own label, and
  every concrete cell alias is an `LDeriv` alias. `LDeriv` relabels a
  plain origin at a labeling point, passes labeled facts unchanged, and
  joins cells whose pointers' facts `meets` (the same labeled origin, or
  a plain origin against any label of its site: the wildcard bridge).
- `label_removal_only`: erasing labels maps every `LDeriv` derivation
  onto today's `FDeriv` (labels only remove answers).

Obligations left open:
1. FAITHFULNESS (built into `RDeriv.clab`): only instances initialized
   as `t` pass a `lab t` edge. A labeling point must be an instance's
   first typed write; an instance passing it already initialized
   otherwise is memory reused for another type, observable only through
   a stale pointer (use after reuse). Not checked statically; the rule
   check (plan 3.9, L4) reports a labeled fact arriving at an
   incompatible labeling point or access.
2. Realization: the solver keys cell clusters by labeled roots and
   realizes `meets` between a plain and a labeled origin as a pairwise
   bridge (as VX realizes the wildcard shift), not a merge. That the
   bridge realizes `mal_join` with `meets` is argued as for VX, not
   restated.
3. Composition with named cells (labels × names in one solve) is not
   stated; both refine cell keys independently, and each theorem is
   about one dimension.

## Keys (Keys.lean, 2026-10-03, plan-named-cells 3.10/3.11)

The first statement against a CONCRETE semantics. A program is a set of
statements (alloc, fnaddr, copy, field, lab, i2p, load, store, icall,
icallRet, and the correlated call `dcall` for `p->fn(p->data)`), any of
which may run at any time; values are pointers to locations, functions
or data; memory starts as data plus pointers among environment objects.
An `i2p` on data forges an arbitrary pointer. A key denotes locations
(`γ`); a load reads every cell whose key `meets` its own.

Statements (checked):
- `keys_sound` (`propext`): under the three rules and the key
  obligations, every reachable state is covered by EVERY solution closed
  under the rules (not only the least). No identity roots: a cell nothing
  wrote holds data, and by rule (a) data never becomes a pointer.
- `icall_sound` (`propext`): every function an indirect call actually
  calls is in its answer.
- `coarsen_sound` (no axioms): any larger `meets` is sound; union-find
  clusters (transitive `meets`), presolve and SCC merges are coarsenings
  with a precision cost, never a soundness one. Since `keys_sound` holds
  for every closed solution, a realization that merges variables or
  cells is covered as long as what it computes is closed.
- `ProductKey` with `product_meetSound`, `product_meetKSound`,
  `product_fieldCover`, `product_faithful` (no axioms): keys as
  (site, position, instance), meet componentwise; each obligation reduces
  to its own dimension (site by construction, position by `PunFree` and
  address arithmetic, instance by faithfulness).

Hypotheses (the rules; each is what L4 reports when it fails):
- `NoForge` (rule a): no reachable `i2p` reads data. ptrtoint/inttoptr of
  a value that was a pointer is a copy, not a violation.
- `AccessAgree` (rules b, c): every load and store touches a location in
  its access key. For a named access this is `PunFree`; for an untyped
  write whose key excludes certified fields it is rule (c).
- `FieldCover`: field steps (GEPs, the two reads of `dcall`) cover the
  concrete address arithmetic.
- `Faithful`: an object passing a labeling point is one the label
  denotes (no use after reuse).
- `AllocCover`: an allocation's result lies in its site key.
- `MeetSound`, `MeetKSound`: key-domain properties.
- `EnvInit`: environment memory holds no code pointers, and its pointers
  are described by `envCnt`.

Obligations left open:
1. Graph fidelity: the statement set encodes the IR (every pointer-moving
   instruction, summary atom and special case is a statement or a sound
   over-approximation of one). The 3.10 special-case table is the
   inventory; not mechanized (cf. F9).
2. Environment model: which objects are environment sites (argv/envp,
   the fuzzer buffer, one per extern global, one per bodiless callee
   without a summary, one per formal of a never-called function) and the
   enumerated runtime code-pointer sources (dlsym; kallsyms, module
   symbol resolution, firmware tables) as `fnaddr` statements with a
   ledger line. Stated in the plan, not in Lean.
3. Calls are modeled through indirect calls; direct calls and returns are
   copies (context-insensitive). Concurrency is interleaving of the same
   statements (flow insensitivity covers it).
4. Undefined behavior: a load or store through a non-pointer does not
   step; executions that do it are outside the theorem.
5. The existing results (`solver_complete`, named cells, labels,
   channels) are not yet restated as instances or realizations of this
   model.
6. The rules are checked by the solver's own facts (L4), not proved:
   the report is the deliverable for programs that break them.
7. The environment (`--cfl-alloc-origins`, plan 3.16): what code with
   neither IR nor a summary does is fixed by `--cfl-outside`.
   - `pure` (default; whole programs only, a partial corpus refuses it):
     such code writes nothing, calls nothing and keeps nothing it is
     given; a call to it returns no object, an uncalled function's
     formals take nothing, extern globals hold only what the program
     writes. A premise, UNSOUND for code that does otherwise; the rule
     report's outside rows (plan 3.48) say per indirect call where it is
     load-bearing.
   - `roots`: each formal no call reaches, each bodiless call result and
     each vararg is an environment object with environment content (in a
     partial corpus also exported formals and visible globals): one
     object, ENV, whose memory is the closure of what escaped; outside
     code reads and writes what it holds and may call any function whose
     address it holds. In `Keys.lean` terms ENV is one site key with the
     wildcard position and `EnvInit` becomes "the initial memory and
     every outside step are covered by ENV's cell"; the outside steps are
     not stated as statements yet.
   - Both modes (plan 3.48): outside code honors the type of what it is
     handed. It reads and writes only within the subobject it received
     (per content cell: the struct at the offset, else the array holding
     it, else the cell; an unlabeled object whole) and what that
     subobject points to, never stepping past it. Under `pure` this is
     part of "writes nothing"; under `roots` it is the whole claim of the
     per-cell exposure. Not mechanized; printed with the rule report's
     assumptions.
8. `va_list` is modeled as memory (va_start writes the variadic
   arguments into the va_list object, va_arg reads it); the lowered
   va_arg sequence is recognized from GEPs that index `__va_list_tag`.
9. Tagged fields (plan 3.51) key a pointer field F by a sibling D the
   program writes with it and tests before reading it. The invariant the
   implementation approximates: a writer W's tag set is the set of D
   values that can hold while W's content is in F and F is read; a read
   under a stable test P admits W iff some value in that set satisfies P.
   - Constructors: a tag store t gives its values to the last F writers
     of its object before it, L(t). L(t) is a backward walk stopping at F
     stores of the object and at direct calls whose summary must-writes F
     of the parameter the object is passed in. It is open at the entry,
     at an F store of another identity, at a call that may write F other
     than through that mapping, at an indirect call when an address-taken
     function may write F, at a bodiless call under `roots`, or at the
     walk bound. An open t is also a retag: its map applies to every
     writer.
   - A writer whose content can be read (a tested read, a call that may
     make one, a return) before its object's D or F is rewritten is
     observed under the tag it found: the values of the last D writers
     before it, or every tag when that set is open. A tag write whose
     value may compute from the tag it overwrites (an own-tag map, or not
     evaluable), or a callee whose last D writes do, observes the found
     tag too: it is the map's input (2026-10-10 fix; the walk used to
     stop at any D write, and a writer whose only later D write was
     `flags |= x` got an empty set).
   - Install is per field F, after every candidate D is judged. Writer
     keys do not name D, and a read keyed by several Ds admits the
     intersection of their admitted sets, each a sound superset of the
     writers whose content can reach it. (2026-10-10 fix: per-D key
     names made a second D's reads list cells no writer writes.)
   - Products: a predicate reading an integer tag D1 and a
     function-pointer tag D2 is judged on the pair. Writer i is admitted
     iff some pair in A_i x B_i passes, where A_i and B_i are its
     component sets, each sound for its own D. Their product contains
     every (D1, D2) the writer's content can be read under.
   - Function values: a function-pointer parameter of an exported entry
     whose address is taken (or any exported function in a partial
     corpus) holds its call sites' arguments or the outside domain: NULL,
     -1, one value for every function outside the corpus, and the
     exported functions. This premise (the 3.48 "outside honors types"
     premise applied to function values) is checked after the solve:
     internal functions reaching exposed cells or bodiless calls, and
     indirect calls in the corpus resolving to such an entry, are
     reported as breaks, not repaired.
   - Return identity: a call's result is a fresh identity R. A walk that
     reaches R's definition (the call) takes the callee's return summary.
     - The summary is the union over return paths of the last writes
       before the return to the returned value's identity inside the
       callee.
     - At -O0, each store into the %retval slot that only branches to the
       return block is a path.
     - A path that reaches the callee's entry with an argument as the
       returned value continues before the call on that argument.
     - Any other path reaching the entry, or a recursion through a return
       in progress, is open.
     - A summary computed while parameter summaries are still being solved
       is not memoized.
   - Outside domain and outside callers, as one exposure question (Q1).
     - Pre-solve, a function's address may reach the outside unless every
       use is a direct call, a comparison, or a store into a struct field.
       The field case rests on the printed premise that the outside
       performs no field access on what it is handed.
     - The outside domain of a pointer parameter of such a function is
       NULL, -1, the outside's own functions (bodiless ones included), and
       that pre-solve set. Its parameters hold their call sites'
       arguments or that domain.
     - After the solve, the 3.48 exposure pass computes the exact set. It
       also exposes the arguments of indirect calls whose callee depends on
       an outside boundary: a dlsym'd entry point, followed through local
       slots and callee returns.
     - A function in the exact set that the pre-solve set excluded is a
       break, reported; so is an indirect call in the corpus resolving to
       an outside-entered entry.
   - Tag values read at a load (rule iii). An own-tag term is the
     current tag at its store only if no write of D, no call that may
     write D, and no redefinition of the identity can come between the
     load and the store. Otherwise it is the set that held at the load:
     the last D writes there when closed and constant, else an image of
     any tag of the field.
   - x-masks: bits of a tag value taken from another object's tag of the
     same field are the projection of U, the values the field holds
     anywhere in the program. U is the least fixpoint of the field's
     constants (0, memset fills, constant writes) under every tag write's
     maps, guards ignored. Sound because another object's tag is some
     value of the same field, so it lies in U. If U widens, the bits are
     free.
   - Out-parameter writes: a direct call handing &identity->F to a callee
     that writes through that parameter on every return path is an F
     writer at the call (F walks only).
   - A memset fill covering all of F and D is the last F writer before its
     own D write, so by the last-writer rule it is a co-write with the
     fill constant as its tag, not a retag of every writer.
   - Per-path guards: for an open retag with no dominating test, the
     stable tests on its identity's own D are cut; if the F walk then
     closes, every open path crosses a cut edge, and each such path's map
     applies under its own edge's test. Only edges an open path reaches
     guard.
   - Parameter-pair tests: a read of F passed as parameter j of a direct
     call, with the same identity's D (through casts) as parameter k, both
     loads and the call in one block with no write between. The callee's
     parameters are values, so a use of j dominated by tests on k
     (branches, or switch edges: case values, default = none of them)
     runs only when the tag satisfies them. The read admits the union
     over uses; an untested use makes it an untested read. This does not
     separate the uses inside the callee (they share j's value).
   - A union slot keyed by tag also drops the 3.17 census keys of that
     slot on every access before the tag keys go in: an access the tag
     keying leaves unkeyed then reads every write of the slot, a superset.
   - Unions: a union member with pointer stores is one field F. Every
     store of any width or type is an F writer, and its pointer and
     pointer-width integer loads are F reads. This is the same rule with
     no new premise: a tested read admits writers by tag and takes
     whatever facts the admitted writers' stored values have (an integer
     store's facts are its integer-provenance facts). In the solver, a
     keyed slot's content cell is split into U (unkeyed writes) and
     P = U + keys. A cell minted before its object was typed is split
     when the object is typed. P inherits every link U had, so a read
     linked before the split still sees every write.
   - A test is stable when no D write can come between it and the access
     (the last passage), and a retag's own-tag map applies only to tags
     its stable tests admit.
   - Identity: by reaching definitions within a function, and by
     direct-call parameter mapping across calls. An object reached through
     a load is another identity.
   - The certificate (every write to D's bytes named, a char/scalar data
     store, or watched in the solve) and the in-solve flips (byte copies,
     watched stores) make unnamed writes checked, not assumed.
   - Alias assumptions. Where a walk would give up because a call, a
     store or a read of another identity might touch the walked object's
     field through an alias, it records the assumption that the object the
     identity points to is not one those accesses reach at that field.
     The access set is computed before the solve over every function the
     call's possible targets may run. The solver marks the objects arriving
     at the identity's pointer and at each access's base pointer; one
     object at both, at the same field position (or at an unknown
     position), fails the assumption and flips the pair. Flips only add
     edges (keyed cells feed the unkeyed side), so the solve stays
     monotone: its fixpoint is the least solution of the constraints plus
     the flips the facts force. Facts that would have failed an assumption
     still arrive, because nothing removes a fact. That is why a checked
     assumption is sound.
   - Tag sets past 4096 values widen to their known bits (agreeing bits
     known, the rest free); tests over a widened set evaluate as may-hold.
   - Composition. A call between a test and a retag is a function from D
     values to D values: the union over the callee's return paths of the
     composed D writes on each path (the identity for a path with none).
     It is applied to the values the test admits, not replaced by
     "anything". A tag write in a callee that the incoming content can be
     read under (its last-writer walk reaches the callee's entry) is
     accounted at the call sites. Its map is guarded by its own stable test
     and composed after the effect from that test. It goes to the last F
     writers before each call; when those reach the caller's entry, it
     becomes the caller's, or a retag if the caller has callers the
     program does not show (address taken, or a partial corpus).
     Recursion is solved as rounds from the empty effect. This rests on
     the premise, printed with the report's assumptions, that a call
     returns only through its returns: longjmp is not modeled.
   - Reads are stable against F writes only. A D write between a test and
     a read leaves the content the test spoke for in place.
   - Inside a region dominated by a pointer-equality edge (the true
     successor of `==`, the false one of `!=`, entered only from the test),
     the two pointers name one object, for the evaluator and every walk.
     Outside it they are two objects. A redefinition of either pointer
     ends it, since the merged names are definitions.
   - Refinement, not yet implemented: the access set of a skipped indirect
     call could be the solver's resolved targets for that call instead of
     all address-taken functions. This is admissible by prefix induction.
     Targets only grow. A real write within any execution prefix is made by
     a target the solve has already resolved on that prefix. So an
     assumption that holds against the resolved targets at the fixpoint
     holds against every real write, and the check stays monotone in the
     failing direction. Without it, the re-entrant failures (the walked
     function's own access reached through address-taken reach:
     sqlite3_str_reset, jsonZero, propagateConstants) fail soundly but
     needlessly.
   - Identities are definitions: mem2reg's for -O0 slots; an element
     address by its base and index definitions; reloads of an escaping slot
     in one block with no memory write between. A walk that crosses a
     definition of its identity's parts stops there (another object).
   Not mechanized. Premises: bodiless calls write and read no slot under
   `pure` (item 7); writes the analysis has no statement for are out of
   scope (item 1).

## Byte-copy walk: periodic runs are skipped (CellSolver copyRegion, 2026-10-11)

A byte copy of L bytes walks positions k = 0..L-1. At each position it
takes the (source object, destination object, source key, destination
key) pair. Each new pair adds that pair's edges once; a repeated pair
does nothing (`seenAt`). The walk now skips work it knows repeats:
- *Statement.* Within a run, both sides keep their objects, and each
  side's key is a periodic function of k (period ps, pd). Then the pair
  at k equals the pair at k - lcm(ps, pd). So every position after the
  first lcm(ps, pd) of the run repeats a pair already in `seenAt`. Jumping
  to the run's end yields the same new pairs, in the same order, so the
  edges and the tagged-field flips are the same.
- *Periods.* foldIn folds every element of an array to element 0, so the
  key is periodic with the element size up to the array's end
  (foldPeriod, the outermost array). Other periods:
  - an object of repeating layout: the layout's size;
  - a byte buffer: 1;
  - a learned element: its period;
  - a scalar outside any array: none (the run is walked).
- *Run ends.* A run never crosses:
  - a change of either object (a header's trailing object begins);
  - the end of a non-repeating layout object, where the walk stops;
  - the end of the array that gave the period.

`copyKey` memoizes foldIn per (layout, offset in one instance). It is the
same function as `contentKey` on layout objects, which is checked by the
gates.

Not mechanized. Checked by executions:
- consumer outputs byte-identical (libpng, SoK sets, libjpeg ×4);
- httpd O0 to completion: icalls JSON and log identical;
- tcpdump O0 at 1,300,000 pops: census log identical.

## Bytes is not a label; written labels; label extent (CellSolver, 2026-10-11, plan 3.53 rule 1)

An unlabeled object is unnamed: its cells are its raw byte offsets. Three
changes:
- **Writes label, reads do not.** A member step of struct T at offset 0
  labels the object only when the step's address is written through: a
  store's address, or a memcpy/memmove destination, through further GEPs
  and casts (`addressWrittenThrough`). A copy into an unlabeled object
  from its start gives it the source's struct (effective type).
- **Bytes is not a label.** A variable byte index (stride 1, a byte walk)
  into an unlabeled object yields the object's any-offset cell, which
  writes and reads all of its content cells. A byte copy to or from an
  unlabeled object (no learned element size) uses that object's
  any-offset cell on its side.
- **First typed use.** An object used as bytes while unlabeled (a
  variable byte index, or a side of a byte copy) keeps that use. A later
  struct write does not label it: a rule (b) row ("struct written into
  storage used as bytes"), reported, not admitted. The write still flows:
  its step yields the raw cell, or the any-offset cell.
- **Extent.** A label covers one T at the start. What follows is decided
  by the allocation's size:
  - a multiple of sizeof T: an array of T;
  - exactly sizeof T: one T;
  - T plus trailing data, or a size that says nothing: one T followed by
    an unknown trailing object. "T plus data" needs a positive constant
    term of at least sizeof T. A negative term (-O3 folds `len - 8*n - 8
    + 1` into a sum carrying -8) is no header size, so such a size says
    nothing.
  A T-typed index (a variable index or walk whose GEP steps over elements
  of T; a stride that only equals sizeof T is no evidence) on the latter
  makes it an array of T (`extendToArray`). Any other variable index from
  the T, or one whose extension is refused, also reaches the trailing
  data's any-offset cell: the T is not known to be an array of one. The trailing object's cells merge into
  the header's element at offset + sizeof T modulo sizeof T. Its address
  facts move there, it forwards to the header from then on, and its
  any-offset cell is linked both ways to the header's. A trailing object
  already labeled, or of a learned element size, refuses the extension
  (counted). One label per allocation: a trailing object that is there
  because the size said nothing never takes a label of its own. A write
  of another struct there is a rule (b) row, not admitted (the write
  flows to its raw cell).
- **Same T after the header.** A write of the header's own T into the
  trailing object right after the header makes the allocation an array
  of T, whatever the size said: T plus data, or a size that says nothing.
  This is a renaming inside the allocation. Any bytes beyond the array
  (binutils' carsym block: a string table after the entries) run over
  the elements, as any byte access on a labeled object does. Before this
  rule, a sized header+tail walked by `p++` minted a trailing object per
  step, each the header of the next: no fixpoint.
- **Keyed accesses wait for a label.** A keyed union access through an
  unlabeled object waits until the object is labeled, then links keyed.
  At the fixpoint, accesses still waiting link unkeyed, and the solve
  continues.

Identity: a struct the linked IR merged away under another name (two
isomorphic structs, one IR type) names its object's cells by its
debug-info identity, from the declared variable, formal, global or copy
source; offsets stay the IR layout's. Names never decide answers here
(unification by name is a measurement switch), so this changes reports
and checks only.

Hypothesis (the naming rule as it stands): an object's layout is its
allocation site's declaration when the site has one (plan 3.53 1b: the
struct the receiving variable's debug type points to, from a dbg.value
on the result or the dbg.declare of the slot it is stored to; else the
struct of the typed writes through the result in the allocating
function), and otherwise its first typed use in solve order. The site
label is fixed at mint time, before any solve-order write, so it removes
the order dependence wherever a site declares; char, void and integer
receivers declare nothing. A later incompatible use (a struct
written into storage used as bytes, or into an allocation laid out as
another struct) is reported as rule (b), not admitted as a layout. The
other order needs no row: a byte access on a labeled object runs over its
fields (the any-offset cell). The order dependence is the old model's
(bytes, then struct, was never labeled).

Statement:
- **Labeling renames within one object.** The cells it merges are cells
  of the same object at offsets the label folds together; no two objects'
  cells merge. A raw-offset cell +k becomes the cell of the field holding
  k, and its facts and links go with it (refold).
- **Every access stays sound before labeling.** A raw cell is exact for
  its byte offset. The any-offset cell over-approximates every byte of
  the object. A variable byte access or an unlabeled copy side therefore
  reaches every cell it could touch, as the single bytes cell did.
- **The array extension merges the same memory.** p[i].x (header cell x)
  and p[1].x (trailing cell at sizeof T + x) are one byte once the object
  is known to be an array, so the merge is a renaming inside the
  allocation. Without the extension, a variable index from the T reaches
  both its own cell and the trailing data's any-offset cell, so p[i].x
  meets p[1].x either way.
- **A waiting keyed access is linked before the fixpoint is final.** It
  is linked keyed if the object gets a label, unkeyed otherwise. The
  solve does not stop with an access unlinked.

Not mechanized. Checked by executions:
- consumer outputs (libpng, libjpeg ×4) byte-identical;
- httpd and tcpdump to completion (see the commit);
- test/cfl-smoke.sh;
- test/tagged-gaps.sh (the waiting keyed access restores
  t_tagged_both/compose/fnptr, whose reads stepped before the writers
  labeled the object).

## Confirmed fresh wrappers (Summaries confirmFreshWrappers, 2026-10-11, plan 3.53 follow-ups 1 and 2)

A function with a body and no summary is confirmed as an allocation
wrapper when three conditions hold:
- R1: every returned value traces, through phis, selects, casts and spill
  reloads, to null or to a call of a fresh source;
- R2: the fresh value has no other use than reaching the return, the
  classified init stores and composed init helpers;
- R3: the body has no other pointer side effect.
A confirmed wrapper's own call sites then mint one fresh object per site
(FRESH), and its body is still analyzed (BODY): its calls stay in the
graph, but its result is not the callee's object.

A fresh source is a FRESH callee (from the file, promoted, or
hardcoded). Its other atoms, when present, are inherited with the formal
that reaches the argument they name:
- CPY(ret<-argK) (the strdup shape) becomes CPY(ret<-arg_i);
- ALIAS(ret=argK) (the realloc shape: FRESH covers realloc(NULL, n), the
  alias carries the old object) becomes ALIAS(ret=arg_i), for each formal
  i of the wrapper that reaches argK. Null may also reach it (the
  realloc(NULL, n) path). Anything else reaching it rejects the wrapper
  (`alias-src-untraced`).
A callee with any other atom is not a fresh source.

Statement:
- **A confirmed wrapper's result is the callee's result, renamed per call
  site.** By R1, each return is null, a fresh object, or (under ALIAS) the
  object passed in arg_i. By R2 and R3, no other reference to the fresh
  object leaves the wrapper. So the object is reachable only through this
  call's result, and a per-call-site identity loses no flow. The ALIAS
  atom carries arg_i's facts into the result, as the callee's atom
  carries argK's. Using the old pointer after a moving realloc is
  undefined behavior (reported, not modeled; plan 3.30).
- **The promoted line is what the file would say.** The engine emits the
  summary-file line (`ConfirmFresh: LINE`). A hand realloc row that the
  engine confirms with the same line is removed from `func_summaries.txt`:
  bfd_realloc and bfd_realloc_or_free. Realloc rows the engine cannot
  confirm stay: sqlite3's realloc family (dispatch through xRealloc) and
  png_realloc_array (malloc_fn, then a copy).

Not mechanized. Checked by executions (see the commits 07be17c and
follow-up 2): consumer outputs, httpd and tcpdump to completion,
test/cfl-smoke.sh, test/tagged-gaps.sh.

Calls that do not return (Fable 2026-10-12). R3 exempts a call marked
noreturn (the attribute on the call or on its callee) whose block ends
in unreachable. Examples: bpf_error, png_error, __assert_fail.
- **Statement:** a path through such a call never returns the wrapper's
  result, so R1 and R2 are unaffected on it.
- **Effects are still analyzed.** BODY keeps the body, so every effect
  of the call is analyzed as part of it, as before the exemption. That
  includes a longjmp back to an outer frame (bpf_error longjmps to
  pcap_compile's setjmp). The longjmp moves control, not data. The
  flows-to facts are flow-insensitive, so it does not change them. The
  one place control transfer matters is covered by the premise in item
  9 of the tagged-fields gaps: a call returns only through its returns,
  and longjmp is not modeled.
- **Rows removed:** the redundancy report then confirms sqlite3PageMalloc,
  png_malloc and png_malloc_array with the same line, checked as a set,
  so their hand rows are removed.

Recursive wrappers (plan 3.53 rule 3, Fable 2026-10-12). A candidate on a
cycle of direct calls among unconfirmed pointer-returning functions is
judged at the greatest fixpoint. The candidate set is assumed fresh: a
call into it is a fresh source. Candidates that fail R1 to R3 under that
assumption are removed, and this repeats until the set is stable. The
survivors are promoted (`_objalloc_alloc`, which returns its own
recursive call or a carve). A recursive hand row is checked the same
way in the redundancy report, with its own calls assumed fresh.
- **Statement:** a survivor's result is fresh, by induction on call
  depth. At depth 0 every return is null or a fresh source outside the
  set. At depth n + 1 a call into the set returns, by the hypothesis, a
  fresh object at depth n. A call that does not terminate returns
  nothing.

## Pool carves (Carves.cc checkPoolCarves, --cfl-pool-carves, 2026-10-12, plan 3.53 rule 3)

**Invariant.** At a carve, every byte at or above the cursor has been
unwritten since the chunk's refill (a rewind is FREE). So the carved
region has no content to lose when it becomes a fresh object. What makes
this hold:
- a single cursor that only moves forward;
- no second route into the chunk: the chunk-base check, and no taken
  field addresses;
- rule (a), for a carve result's own overrun.

A pool bumps a pointer through the free space of a chunk it allocated
and hands out the pieces. Without carves every piece is the chunk object
(one origin for every bfd_alloc). With them, each carve site of a
certified pool is its own allocation site: the carve result is a fresh
object, and the flow from the chunk pointer into it is cut. Each object
is laid out by its first typed use (rule 1).

**Forms.**
- Before-bump: `p = load H; store H, p + n`; the result is p.
- Minus-len: `store H, (load H) + n`; the result is `(load H) - n`.
- Counter: `store C, C - n`; the result is `(load M) + C`. M and C are
  fields of one struct.
- Header: `c = malloc(HDR + n)`, with c stored into a chunk field; the
  result is `c + HDR`, the n bytes past the header. The header fields are
  ordinary cells of the malloc object.

**Pool fields.** A bumped field H (or counter base M) is a pool field
only when an allocation refills it somewhere. A bumped field that is
never refilled is a cursor over data. It keeps today's flow and is
counted.

**Checks.** The hypothesis of carve-as-fresh is that a chunk's carved
contents are reached only through carve results. Two static checks
establish it:
- **Handle fields.** These are the pool fields plus every field a chunk
  pointer is stored into (closure). Every load of a handle field is used
  only by:
  - the forms;
  - stores into handle fields;
  - icmp, ptrtoint, pointer difference;
  - free, memset.

  The chunk's free-space start (`chunk + HDR` stored into H) and -O3's
  joins of a reload of H with a refill's free space are the H route,
  covered by this check.
- **Joins.** A phi or select is a free-space value, so the carve may sit
  on it, only when every incoming value is one: a reload of the cursor,
  a chunk's free-space start, null, or such a join. Otherwise the carve
  sits on the free-space operand, and the other operands keep flowing.
  This is the allocate-unless-provided shape: `phi [carve, entry]` in
  bfd_hash_newfunc's family, and `phi [carve, string]` in bfd_hash_lookup.
- **Chunk bases.** An allocation stored into a handle field is accessed
  only:
  - at its header fields;
  - by stores into handle fields;
  - by free, compares, memset;
  - by the carve.

  A GEP at or past the header that is not the carve refuses the pool.

- **One forward cursor.** A pool hands each piece out once, so:
  - a pool has one bump or counter field;
  - that field only moves forward.

  A cursor that also moves back (`top - 1` stored) is a stack, and two
  cursors through one chunk are a queue. Both read back what they handed
  out (libyaml's token queue and state stacks, refused). A handle field
  that receives a pointer into the free space (a saved cursor, a queue's
  tail) is read as a free-space pointer, not a chunk start.
- **No field addresses taken.** A handle field whose address is taken
  (`&q->tail` passed to an extend function, a memset over the struct) is
  written where the checks do not look, and that refuses the pool.

Any other use refuses the pool, and the refusal is printed with its
site. Fields are keyed by debug-info struct identity (IR-merged structs
stay apart), with the IR type as the counted fallback.

**Three hypotheses under rule (a)** (no forged pointers), not checked:
- **The pool's own arithmetic is exempt.** `R = load H - n` and
  `M + C` compute a pointer into the chunk from a field value. They are
  forged pointers in the sense of rule (a), admitted only as the
  recognized forms.
- **A field at offset 0 is accessed by its type.** Its address is the
  struct's address. Passing the struct (`objalloc_alloc(o, n)`) is not a
  taken field address, so a callee is assumed to reach the field through
  a typed access the checks see.
- **A rewound value is a carve result of the same pool.** A store into a
  bump field whose value is a formal, or a join of handle values with a
  formal (objalloc_free_block's `o->current_ptr = b`), is a rewind with
  FREE semantics: the pieces after it are dead. The static check cannot
  see across callers that b came from this pool.

**Statement.** In a pool that passes both checks, under the two
hypotheses, the carved bytes `[R, R + n)` are reached only through R and
pointers derived from R. A carve object therefore loses no flow:
- the handle fields carry no pointer into program data, since their
  loads have no data use;
- a chunk base reaches the free space only through the carve forms;
- the bump makes the pieces of one chunk pairwise disjoint until a
  rewind.

**Temporal abstraction.** Rewind as FREE is the abstraction of malloc
after free: memory handed out again is a new object, and content
written through an older carve is not read through the new one. The
analysis is not temporal. The assumption is the one recorded for
lookaside and objalloc reuse in func_summaries.txt.

**Confirmer.** A carve result is a fresh source for R1. The certified
pools' bookkeeping (handle-field stores, the bump, rewinds, ptrtoint of
handles) is exempt from R2 and R3, because it is the pool's own state
that the checks cover. bfd_alloc and bfd_hash_allocate are then
confirmed, and so is _objalloc_alloc (greatest fixpoint); their hand
rows are removed.

Not mechanized. Checked by executions; see the rule 3 commit's gates.
