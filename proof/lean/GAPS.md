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
