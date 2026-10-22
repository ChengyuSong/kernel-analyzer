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
   inventory; not mechanized (cf. F9). A constant integer is not a
   carrier; a ptrtoint constant is a value node of its object (Fable
   2026-10-13, --cfl-cells): an integer constant derived from one pointer
   (a ptrtoint chain, a rebased inttoptr) gets its pointer's value node,
   and the factory's shared constant-int node ends the solve without a
   fact (asserted). Before, a store of `ptrtoint(@g)` seeded that shared
   node and every integer constant read it (the kernel's ERR_PTR arms
   carried secondary_startup_64 to every list reader). The solved-summary
   prover evaluates such a constant as its global (a folded chain as an
   unknown value), not as nothing: an empty value made the store vanish
   from an adopted OK-EMPTY summary (both solvers' prover: a soundness
   fix, the flows-to consumer outputs may gain pairs, attributed).
   An atomic exchange or compare-and-swap moves its integer operands
   like a store and a load (Fable 2026-10-14): at -O0, clang lowers
   __atomic_* through a slot (`store ptr p, s; v = load i64, s; atomicrmw
   xchg q, v`), and the integer load fed only the atomic, which no
   use-side rule admitted, so the exchange stored nothing (both solvers).
   An atomic's stored value (xchg's value, cmpxchg's expected and new
   values) flows onward like a store's value operand, and its old value
   (xchg's result, cmpxchg's first field) is a load of its slot. At -O2
   the atomics take pointer operands and were already exact. (A finding
   on the way, withdrawn: atomics are NOT nameless hubs under cells;
   every cells access goes through its pointer's dereference node, and
   names come from the field edges and object layouts.)
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
   - Set tests (Fable 2026-10-17, (T); reads only): a block dominating the
     read that is entered only on edges of tests of D on the read's object
     (`t == a || t == b`), or, as -O0 emits it, the edge of a branch on a
     phi of conditions (`phi i1 [true, P1], [c2, P2]`: a constant entry
     equal to the edge's value through its block's own test edge, a
     condition entry through that condition on one load of D; a constant
     entry that is not the edge's value never takes it). Whichever entry
     control came through, its condition held: D satisfies one of the
     alternatives. Each alternative is stable from its load to its branch
     (which may be another block: the stretch, not back through either
     block, writes no F of the object and redefines no pointer of it) and
     from the edge to the read, every test block of the set left out of
     the region.
   - Dispatch tests (Fable 2026-10-17, (T); reads only): a switch
     dominating the read on D, or on a value read from a constant 2-D
     integer table one index of which is D (binutils' `switch
     (link_action[row][prev])`; an -O0 local with one store between).
     The edges that reach the read without passing back through the
     switch decide: D is one of the values whose table entries, in any row
     (the other index is not followed), the switch sends along such an
     edge; for a switch on D itself, the case values of such edges, and
     no test when the default edge is one. An index read through an -O0
     local with several stores is each stored value: a constant among
     them that the switch sends along such an edge leaves D untested (on
     that path the index is not D); one it does not send is no path to
     the read. Stability as for set tests, from D's load to the switch,
     then from each such edge to the read.
   - Evaluator gap: -O1 folds `t == 1 || t == 2` into `t - 1 <u 2`, and
     the test evaluator has no add or sub, so such a test is no test
     (the read untested, every writer admitted): sound, imprecise; for
     after (T).
   - A union slot with a tag pair is keyed in two schemes (Fable
     2026-10-16): the tag keys of the pair (F, D) and the 3.17 census
     member keys of the union slot holding F (keyed by the union's own
     offset, struct.S+off#member). They are two partitions of the same set
     of writes, each with a catch-all: "every member" (struct.S+off#?) and
     "every tag" (struct.S+F#!t?). Every write over F's bytes carries a key
     of each scheme: its member key or the census catch-all, its tag key or
     the tag catch-all. Every read carries one scheme's keys and that
     scheme's catch-all: the tag keys where a stable dominating test of D
     keys it (a checked read), else its census member key (the user's
     2026-10-07 assumption, an UNCHECKED read, unchanged). A read keyed by
     neither reads the whole slot: every key, both catch-alls and the
     unkeyed cell. The unkeyed cell (what neither scheme types) is read by
     every read of the slot, in either scheme. So a read in either scheme
     meets every write of that scheme (its keys, its catch-all, the unkeyed
     cell), every write is in both, and no read misses a write; a tag-keyed
     read is not widened by a write the census alone cannot type.
     Asserted: a tag-keyed read carries only its pair's keys, a write of F
     a key of each scheme (a catch-all counts). Only where the census keys
     the slot (an access of F, or another over F's bytes, carries census
     keys); elsewhere a pair keys as before, one scheme: a tagged write its
     key, an untagged one the unkeyed cell, a read its writers' keys (both
     schemes on a slot with no census keys only multiplied key cells:
     tiffsplit-O0's tiff+816 method-field pair did not reach its stop).
     The census prints its UNCHECKED total before tag keys; the tagged fields print how many of
     those reads a tag now keys and the net count. Tag keys are spelled
     "#!t..." (no member or function name starts with '!': bfd.tdata's
     member tekhex_data did start with "t"); another mechanism's keys on an
     access of F refuse the pair before any key changes. Before, the census
     keys were looked for under F's own prefix, never found for a member
     inside a union, and the pair was refused as "already keyed otherwise"
     (bfd_link_hash_entry.u.i.link once the census typed u's members).
   - Product keys, a read of both schemes (P3, Fable 2026-10-17): on a
     slot keyed in two schemes, every write over F's bytes is filed under
     its (tag key, member key) products (each a catch-all where the write
     has none), the two partitions above as one partition. A read in one
     scheme reads every product with its scheme's component: the same
     writes as before. A tag-keyed read that also has a census member key m
     (the key the census gave it before the tag keys replaced it) reads the
     products (t, c) with t among its tag keys or the tag catch-all and c in
     {m, the census catch-all}. So it meets every write its tag admits
     except those the census types as another member: excluded by their
     member name, under the name-compatible-stores rule (the user's
     2026-10-11 principle, a store of another member's name is no store of
     this one; the 2026-10-07 UNCHECKED assumption, now on the write side
     of a checked read). Per read, a listed assumption naming the excluded
     writes ("ASSUMPTION stores of other members excluded by their member
     name (a read of both schemes)" where a container's cursor read rests
     on it). Never excluded: a write the census cannot type (the census
     catch-all, every member), a write of a void * member (the slot's
     unkeyed cell, above). An excluded write the tag admits by a tag of its
     own, retagged or not, is a tag/member disagreement: the two schemes
     disagree about it, and one is wrong for the program. It is reported
     with the retag maps by which the read's tests admit its tag (the
     provenance chain of each admitted value, recorded with the rule
     report), so the disagreement is diagnosed at its source: nm-O0's 17
     reads of u.c.p under `type == common` admit linker.c:1720's u.i.link
     write through elflink.c:1424 `hi->root.type = h->root.type`, a retag
     its own function undoes, tag and content, before returning
     (1458-1467): the census is right, the tag's flow-insensitive retag map
     is the imprecision (for Q2). Sound under the assumption it lists, as
     the UNCHECKED read was; never wider than the tag-keyed read alone.
   - Union members that are structs (plan 3.51 (2), Fable 2026-10-16):
     the union census types an access by member when the access's debug
     type is the member's; when no member's type is, an access at byte o
     of the union with debug type T is of member m if m's layout (nested
     structs and unions, array elements) holds a field of type T at o.
     Several members that fit (binutils' u.*.next at +0 of every member):
     not typed, counted as their own class ("a field several members
     share"), as an access no member fits. Debug info only: a verdict the
     -g build gains, none without it. A union with no access typed by
     member is "no typed access (keyed all)": every access one plane, and
     nothing says one member is used; "one member used" needs at least one
     typed access, all of one member. Before, both read "one member
     used".
   - A union member declared `void *` (cv-qualified or not; Fable
     2026-10-17) is the program's own generic view of the slot (bfd's
     tdata.any). C makes void * assignment-compatible with every object
     pointer (C11 6.3.2.3p1, 6.5.16.1p1), so under the name-compatible-
     stores rule its writes are compatible with every member's reads and
     its reads with every member's writes. A write the census types as such
     a member lands in the slot's unkeyed cell (the census catch-all, read
     by every read of the slot; its own member key is subsumed), and a read
     of it that no check settles reads the whole slot (where it would have
     been an UNCHECKED read keyed by its own member). A read a check
     settles keeps the check's keys: the program's test excludes writes by
     their tag, not by their member name. On a tag slot the write, unkeyed
     by the census, takes the census catch-all among its keys like any write
     the census does not type. Only widens: sound in every case. Before,
     `abfd->tdata.any = bfd_zalloc (...)` was keyed by member any and every
     UNCHECKED read of another member (elf_obj_data, ...) excluded it, so
     the object reached no read but `any`'s (t_cells_union_voidptr.c). A
     possible tightening, not implemented: a void * member is compatible
     with the pointer-typed members only, not with integer members.
     Counted: "UnionKeys: n void* members read and written as any member",
     per member its writes, reads, and the reads keyed by another member
     that now see its writes.
   - A store whose value is a constant address inside a global with debug
     info ((C'), Fable 2026-10-17: the global itself, &g[i], &g.f, any
     constant GEP) is typed by the debug type of the objects starting at
     that address: the global's type walked by byte offset (an array's
     element, the member of a struct holding the offset, each member of a
     union; never a bitfield). Several objects start at one address (a
     struct and its first member; -O3 folds &g[i] into &g[i].first), so
     each level is tried, and the store is the one member that fits over
     every level together (the census's own member match, by type or by
     layout); a level that fits several members, or levels that fit
     different members, type nothing (#?). It rests on the debug info
     naming the global's layout: the address is an object of that type,
     and a store of it into a union names the member whose field has that
     pointer type there. Listed per store in the rule report ("ASSUMPTION
     a store over union S.u typed as member m by its value's debug type
     (T *, a constant address inside g)"). On nm-O0 it types the three
     `&_bfd_std_section[k]` stores into bfd_link_hash_entry.u.def.section
     (coff_gc_sweep_symbol, set_symbol_value,
     assign_file_positions_for_non_load_sections).
   - A void * value or use names no member by layout ((C')): C converts
     void * to any member's pointer type, so `e->u.b.q = mk()` with mk
     returning void * is a store of b whatever void * fields other members
     have at that offset. Before, the census typed it as the member with a
     void * field there (a), and a read of b keyed by its own member
     excluded it: unsound (t_cells_union_void_value.c). Now it types no
     member (#?): only widens. The member declared void * keeps its own
     rule (above).
   - A member by the struct its address steps through (item 0, Fable
     2026-10-18, a gap). A union access whose address steps, at the
     union's start, through a struct S is the member whose debug type has
     S's layout, when exactly one member does. Layouts are compared leaf
     by leaf: each pointer or scalar's offset and kind (pointer, integer
     or float of its width), through nested structs. An array, a bitfield
     or a union inside either layout matches nothing. S's IR name is
     never used, since isomorphic anonymous structs merge across
     translation units. It applies only when the access's own value use
     names no member. A value use naming another member makes the access
     ambiguous, with no precedence either way. Several members of S's
     layout: none, as before. Before, the access was typed by its value
     use alone, so a read of u.i.link that is only copied (elflink.c:4382,
     5239) was "?". Its tag keys then admitted every member's writes,
     because P3's member exclusion needs the read's member. Now it is
     member i, and the other members' writes are excluded by name: a
     per-read ASSUMPTION listing them (the P3 route). Precision comes only
     through that listed exclusion. The typing itself is the program's
     own access, as a member's field name is.
   - A one-field union copy ((C''), Fable 2026-10-17): a store whose
     value, stripped of no-op casts, is a load of the same union field of
     an object (same struct, union offset, offset in the union, type), the
     load feeding the store directly or through an -O0 spill local (one
     store, used only as an address), on a census-keyed slot, is a per-key
     copy of the field, not a write of an unknown member: the solver's
     byte copy of those bytes, its own store edge not made. A key's two
     components have different owners. The member component names the
     bytes: it travels with them from the source (no member is inferred;
     #? travels as #?). The tag component names the destination object's
     state at the write: it is the store's own, the tag keys TaggedFields
     gives the store like any other (the catch-all when it is untagged).
     So a fact under (t, m) at the source lands under (t', m) for each of
     the store's tag keys t' (on a census-only slot, the same key). It
     needs no premise about the destination's tag; taking the source's tag
     too (Q1 (b)'s whole-struct copy, where the tag bytes move with the
     content) would. Listed per copy in the rule report ("ASSUMPTION a copy
     of union S.u+rel between two objects keeps the source's member key
     under the store's own tag keys"). In the container check it is a copy
     of the cursor, not a store into it (Q1 (b)'s treatment): its facts keep
     their keys, under the same-table premise. A function with such a copy
     keeps its body: an adopted atom summary (a proven MV) would move the
     field without its keys. -O3 shapes left as ordinary stores, counted: a
     vector load/store copying several fields at once, a phi of loads of the
     field. On nm-O0: elfxx-x86.c:1934 and elflink.c:1803 among 12 copies.
   - A read's member is typed by its loaded value's uses seen through
     no-op casts (R1, Fable 2026-10-17, a bug fix): clang -O0's typed IR,
     upgraded to opaque pointers, keeps `bitcast ptr %v to ptr` between a
     load and its store into a declared local, its GEP base or a call's
     actual; the walk stopped at the cast and left the read untyped (the
     whole slot), which the design never meant. Only names reads the census
     could name before through the same uses; counted ("n reads typed
     through a no-op cast").
   - A pointer to struct T that no member fits fits the member whose field
     at that offset points to P, when the debug info declares P as T's
     member at offset 0, transitively (R2, Fable 2026-10-17): the C upcast
     idiom (`(struct bfd_link_hash_entry *) hi`, hi a struct
     elf_link_hash_entry *), both names holding for one address. Used only
     when no member fits T itself; the levels of the chain together fit one
     member, or the access is typed by none (several: the shared class). It
     rests on the DI embedding table, and on the premise that a pointer to T
     stored at the slot is meant as the P-typed member. Listed per store in
     the rule report ("typed member m by its value's type T *, which embeds P
     at offset 0") and counted per (T, P) pair, stores and reads.
   - O1's block copies (Fable 2026-10-17, a checker soundness fix): a
     block copy whose destination no field names (a pointer loaded from a
     field, an array) was not checked, although it can write an element as
     a named one does. It is now classified by what the destination points
     to: an element struct (the pointee embeds one), a load of a link field
     or of a closed cursor field (an element), or of a handle field (the
     owner's array): checked as a named destination is (the source an
     element of the same owner, or in the body derived or fresh); a local
     or a global: no element; anything else: open-unproven, listed per copy
     as an ASSUMPTION ("a block copy into no element") and counted in the
     verdict's assumptions. Every failing copy is listed with a count.
   - O1's block copies by name (Fable 2026-10-17/18): "anything else"
     above is decided by the destination's origins by name, a walk over
     the IR alone (no solver fact, so the verdict is the same at any stop
     at which it is read). Steps: casts, GEPs, freeze and pointer-vector
     shuffles, inserts and extracts to their operands; a -O0 slot to the
     values stored into it; a named field S+off to every value stored
     there program-wide (a vector store over it included, lane by lane),
     every global initializer's value there, the values stored through
     its address where that address escapes into a callee (`*ptr = p`),
     and, for a whole-struct copy over it, the same field of the source (a
     source of the same struct, or a local of it with its own direct
     stores); a formal to the actuals of its direct calls; a call with a
     body to its returns; a bodiless call through its summary's
     ALIAS(ret<-argN); an indirect call through the closed code field to an
     element, any other indirect call to the returns of the functions its
     callee holds by the same walk; a load through a pointer, when the
     pointer's names are all named fields, locals and globals, to the
     values stored there or through them. Leaves: an allocation site, a
     local, a global; a certified pool's carve (a chunk); an element: a
     constructor's allocation or carve, a constructor's or a row's result,
     a load of a handle, link or closed cursor field.
     - Verdict per copy: an element among the origins: checked as a
       named destination is; none and no unknown: no element, no
       assumption; any unknown: open-unproven, an ASSUMPTION. Every
       copy's class and origins are rows of the rule report; the log
       groups the open ones by root (the field, formal, call or
       instruction the walk could not pass) with counts.
     - Initializers and empty loads (Fable 2026-10-20, (0), a soundness
       fix). A global initializer's slot is named by every IR named struct
       around it and by the global's debug type (initSlots, shared with the
       object walk's initializer table): a union initializer makes the IR
       type literal, and before, such a slot (every bfd_target vector and
       elf_backend_data in nm) had no name, so a load of its field found no
       value and closed empty. A slot in a literal IR struct of a global
       with no debug type has no name: a load of a name whose struct may lie
       over it in the global's bytes is open ("initializer slots unnamed at
       @G +b"). A load that finds no value is open, never an empty close: a
       named field with no value stored by name, a load through a pointer
       with none through its addresses, an -O0 local never stored, a global
       with no initializer and no store; a global reached through a pointer
       contributes its initializer at the address read. After this an empty
       origin set means null or undef constants only. Consumers of the
       origins: O1's copies by name (empty: no element), R1's covers and
       check (2) (empty: close), the callee walk (requires a function
       among the origins, so empty was never closed there), and object
       identity's initializer table (the same naming; an unnamed slot opens
       it, as before). A local's fields are named as any object's are:
       only a -O0 slot (an alloca used only as the address of its own
       loads and stores) names no field. Before, every address into an
       alloca named none, so a field-0 write into an address-taken local
       (its GEP (0, 0) strips to the alloca; fields 1 and up were named)
       was missing from every list of writes by name (the values stored
       by name, the field feeds, the element stores, the keeps, O1's
       copies) and the cover skipped it as a store into a local. Found,
       not fixed here (the same alloca exclusion, each its own item):
       CellSolver's mod sets, Carves.cc's field key, TaggedFields'
       accessor check, Summaries' pool-field accesses. Cases:
       test/t_cells_container_o1_byname_{vector,vectornodi}.c (a vector
       global initialized through a union: with debug information the
       data load and the indirect call through it close by name; without
       it both are open), test/t_cells_container_o1_byname_localfield.c
       (an element stored into an address-taken local's field 0 and read
       by name through a pointer to it: the copy is into an element).
     - The element premise: elements are exactly the constructors'
       allocations. The block's own checks establish it (O3: every
       insert's ELEM argument and replace/rename's ELEM(arg2) must be a
       constructor's element going only into the owner's storage); where
       one of them is open the block fails, and this classification adds
       nothing to it.
     - The pool premise, once per pool: a carve outside the constructors
       is a chunk apart from every element. It rests on the pool's carve
       certificate (Carves.cc), which is over the pool's handle fields and
       every access to them program-wide, so it covers every caller; a
       carve row's call counts as a chunk only when a certified carve of
       the pool is in it or in a function it calls directly, else the
       walk stops there (unknown).
     - Unknown by design: a formal of an address-taken function (its
       indirect callers are not enumerated by name, and solved targets
       would make the verdict depend on the stop); a formal with no
       caller (an entry); an inttoptr; a bodiless call with no summary
       or a summary that does not return an argument; a field written by
       a block copy from another name or whose address escapes into
       anything but stores through it; any other instruction. Declared
       types are not consulted (C casts them away). Writes through a
       pointer no name reaches are not enumerated, as in every O1 field
       closure: the same discipline.
   - Snapshot holders ((3''), Fable 2026-10-17/18). A candidate is a
     fresh block a block copy fills from the owner's handle array (a
     load of a handle field). It is a holder when every use of it, by
     name (casts, offset-0 steps, phis and selects, -O0 locals holding
     only its values), is one of: a copy into its start from that handle
     array (a handle save); a runtime byte step from its start, which
     begins the element region, or a non-negative step (a zext or a
     constant) within that region; a copy into the region from an
     element of the same owner, of a length read from a named field,
     one field for every element copy in and out (an element save); a
     copy out of it; a null test; free. The
     region's start offsets and every handle copy's length must be one
     value by name: one SSA value, or reads of one -O0 local whose
     stores are its entry-block zero initializer and one store that
     dominates the allocation. So every read made while the block exists
     sees that store, the element region begins exactly where the handle
     copies end, and the two images never overlap. An element of the
     owner by name: a read of a slot of its handle array (the same owner
     shape as the handle save), or of a link or closed cursor field of
     such an element, through casts, offset-0 steps, joins and -O0
     locals. A local's reaching store is the nearest one before the read
     in its block or up its chain of unique predecessors (its address is
     never taken, so no other write reaches it), else every store to it.
     A cycle (`p = p->next`) holds, the greatest fixpoint, as for cursors.
     - Then the block holds only that owner's handle and element content.
       A copy out of its start into the owner's handle array, and a copy
       out of the element region into an element of the owner, are
       moves within one owner: O1 counts them ("restores out of a
       snapshot holder"), they are no failure.
     - The block is two solver objects: the handle image (the
       allocation's own object, a repeating pointer) and the element
       image (one struct T, not repeating, at offset 0 of every
       element-region pointer: the region's runtime steps are dropped by
       name, the steps' field edges cut). The element saves and restores
       are whole-struct copies of T (length sizeof T), key-preserving
       cell to cell.
     - The precision loss, stated: the element image is
       field-insensitive across images. Every restore receives, field by
       field, the union of every save of this owner, not the one image
       the program restores into it. Sound and over-approximate. It is
       exact only where the owner's elements are already one object to
       the solver's view of its content.
     - Premise (entsize): T is the type the owner's constructor allocates
       (the row object's rule: the struct of the constructor's fresh
       block's constant size its typed uses step through, else the
       pointer local it declares; not a size lookup). Every store into
       the length field, walked back through formals to the actuals of
       direct calls with the table pointer and the code field's value
       along, is a path. A table pointer's struct steps are declared
       types, which C casts away (`elf_hash_table (info)` is a cast of
       info->hash), so they cannot decide which tables the owner can be.
       Relevance is by object identity by name, at both ends (Fable
       2026-10-19, (a)): the objects the length field's address can be, as
       (allocation site, offset), for the holder's element-copy length
       read and for each path's size store (its offset carried up the
       table chain). The walk goes through casts, -O0 locals (every
       store), constant steps, joins, formals to the actuals of direct
       calls, a defined callee's returns (an allocator wrapper, every
       return a noalias extern call or null, is its call site), and a load
       of a named field: the objects of the field's writes, defined once
       here (Fable 2026-10-19).
       - A field's writes, for K = (S, o) of width w: (1) every store of
         key K of a pointer (a store of a non-pointer value: OPEN); (2)
         every global initializer pointer named by K: each non-null
         pointer slot is named by every struct around it, the IR's named
         structs and the global's debug type (a union initializer makes
         the IR type literal), and a slot of a global with neither (no
         debug type, in no named struct) opens every field load; (3)
         every other write whose named bytes cover K's: a store named at
         an outer struct, at another offset or of another width, a block
         copy, a memset (structCover over the write's named slot and
         length, a runtime length to the struct's end): OPEN, with the
         count and the first; except (4) a memset whose value is the
         constant 0, a null write: listed with its site and bytes, adding
         no object (zero bytes are null, null names no object; the
         solver's own null). Writes by unnamed address remain the
         standing naming assumption.
       - A union read keyed per key (keysOf: the keys the solver files it
         under, the census's or a tag pair's) reads only the stores of K
         its keys admit (Fable 2026-10-19, (ii)): a store keyed by a key
         the read does not list, nor the slot's catch-all, is another
         member's and excluded; an unkeyed store is admitted. The solver
         files the read under the same keys (applyUnionKeys), so the walk
         admits every store the solver's read can see. A field's result is
         kept per (K, the read's keys).
       - A certified pool's carve (Carves.cc) is an allocation: a carve
         reached directly is its own object; a defined callee every return
         of which is a noalias extern call, a certified carve, such a
         callee's call or null is an allocator wrapper at its call site,
         with the pools it carves from. A refused pool's carve is OPEN,
         named with the pool's verdict. A recursive return adds what the
         other returns give.
       - A cycle through a field read with the same keys adds nothing (the
         least fixpoint: what the other writes give) and is counted apart:
         a field every write of which is cut so is empty, not OPEN as a
         field with no pointer store (nm-O0's bfd_preserve: the saved
         tdata is a load of the slot being walked).
       - (A, Fable 2026-10-19) An element of a handle field's array is a
         slot by name: an address that is one pointer-sized step (any
         index, runtime or constant) from the array a handle field H of a
         checked container holds, where the array is a load of H or a
         value stored into H (through -O0 slots, at most 4 hops: a new
         table before `table->table = newtable`). A load of such an element
         gives the objects of every store into an element of H's array; a
         memset 0 into it is null; a block copy into it, or the array
         passed to a call, is OPEN with its site. Null, a global or a
         formal is no array by name. A load through an -O0 slot holding
         addresses reads each address the slot is stored (a field or an
         element; null adds nothing). Writes into the array by another
         address: the standing naming assumption.
       - (A) An indirect call whose callee is a load of a closed code field
         (O4's: every store into it a function constant, no aggregate copy
         of the owner) returns what its targets return, each as a direct
         callee (an allocator wrapper is its call site).
       - (f, Fable 2026-10-19) A formal of an address-taken function F has
         known callers when F's address only feeds closed code fields:
         every use of F is a direct call, a store of F into a code field
         closed in O1(d)'s sense whose targets include F, or an actual to a
         defined init function that is not address-taken, whose formal has
         one use (at -O0 a store into its slot, the slot read by one load
         and used no other way), the value stored into such a field or
         passed down to another such init function the same way. Then the
         only calls that can reach F are its direct calls and the indirect
         calls through those fields (an indirect call elsewhere would need
         F's address from somewhere else, and there is none), so F's
         formal has those callers' actuals; a cycle through the formal is
         a cycle cut as above. An address in a constant, a second use of a
         slot, an address-taken or bodiless init function, or a store
         elsewhere leaves the formal OPEN, with why it is logged.
       - (R3, Fable 2026-10-20) Formals through constant vectors. A formal
         of an address-taken F also has known callers when each use of F's
         address is a direct call, one of (f)'s uses, or a slot of the
         initializer of a global that is an IR constant (isConstant()): a
         write into a constant is undefined, so no write, named, unnamed
         or with open origins, changes the slot. Each such slot is named
         (initSlots: the IR named structs around it and the global's debug
         type; an unnamed slot, a union initializer at -g0, leaves F OPEN:
         "initializer slot unnamed at @G +b"), and for each of its keys
         S+o: (a) no write in a body lies over S+o under S or under a name
         embedding S there (a constant-zero memset and a store of null
         write no function; a function constant stored in a body is a
         write), and (r) every read of S+o by name is an indirect call's
         callee: each load named S+o is only called, compared, or kept in
         -O0 slots read only that way, and no block copy reads S+o by name.
         F's callers are then its direct callers and every indirect call
         those loads reach as callee (directly or through -O0 slots), any
         base. (a) and the constant global take the role of O4's closed
         code field, so O4's check is not needed; an open base costs
         precision at the actuals only. A writable vector stays OPEN
         ("writable global @G"): nm's elf backend tables
         (elfxx-target.h's `static struct elf_backend_data elfNN_bed`) are
         written at a runtime offset by bfd_elf_set_pagesize (bfd.c:2115
         `*((bfd_vma *) ((char *) bed + offset)) = size;`), and writes
         with open origins may reach them. That store is an integer with no
         origin under --cfl-alloc-origins; proving that per store is a
         lever, not taken. The read side's block copies: a copy whose
         source is read under a struct name reads that name's cells (the
         name premise); a copy with an unnamed source whose known origins
         hold one of F's globals leaves F OPEN; one whose origins are open
         (each source walked once, every address-taken formal open) rests
         on the byte-cell premise of plan 3.53: a byte copy carries no
         code pointer, a pointer copied as bytes would be a leak. Each such
         copy is an ASSUMPTION row of the rule report ("R3 read side"),
         with the log count of copies under another name and unnamed. The
         caller side is not given: a vector function's stores through its
         formal into a caller's local (nm.c:1112's minisyms, filled by
         bfd_read_minisymbols through BFD_SEND) need the call's targets,
         so those writes stay OPEN. A function with no call reaching it by
         name has no caller: its formal stays OPEN ("which has no caller"),
         as for any function never called. The covers' origins
         (originsOf) consult the same callers for (f) and R3; (f) adds no
         cover close on nm-O0. (f) checks the same read side (r) on each
         closed code field it stores into (Fable 2026-10-20): every load
         by the field's name is only an indirect call's callee, compared,
         or kept in -O0 slots read only so, and no block copy reads it by
         name unless the copy is K-to-K (R2's test: its destination is
         named so that K lies at the same place, every overlap of K
         whole); otherwise "not applied, its field K: <why>". The same
         copy clause holds for R3's slots. A K-to-K copy puts the field's
         value at a cell of the same key K, and (r) checks every load of K
         at any base, so a call through the copy is already among the
         callers. The allowed copies are logged per field. (f)'s callers
         include the calls through those -O0 slots: at f86a9e6 a call
         through a -O0 local was no caller of (f), a gap now closed, and a
         load passed on was not checked. nm-O0: struct.bfd_hash_table+8 is
         loaded 2 times, each directly called, and copied K-to-K by
         bfd_preserve_save and bfd_preserve_restore (format.c:130/162).
         Cases: t_cells_container_snapshot_vectorformal{,slot,w,nodi,named,
         byte}.c, t_cells_container_snapshot_fedformal{read,slot,ktok,
         copy}.c.
       - The walk computes the least fixpoint of these rules over nodes (a
         value, a field read under its keys, a handle array's elements): a
         node's objects are the union of its successors', each shifted by
         its step's offset. It is depth-first with Tarjan's SCCs. A node
         met again while its SCC is under way adds nothing there (a cycle
         cut): in an SCC every member reaches every other, so with steps
         summing to offset 0 all members have the same objects up to their
         offsets, and those arrive at the root. Every member of a finished
         SCC gets the root's objects shifted by its offset from the root;
         only finished SCCs are kept, each node's result relative to its
         own offset. A cycle whose steps do not sum to offset 0 (p = p + 8
         in a loop) has no finite set of objects and is OPEN ("a cycle
         through V stepping the offset by n"). Keeping results changes only
         the order in which objects are found, not the least fixpoint: a
         kept result is the fixpoint of its node, and a result not kept is
         recomputed. Past a node budget (200000 nodes per holder) a node
         not yet walked is OPEN ("budget exhausted at V"), counted and
         reported; a result under a budget cut is not kept. This replaces
         the depth limit of 16, which cut the walk without a cycle.
       Anything else is OPEN with its reason (an address-taken formal, an
       indirect call's result, a runtime step, a load of no named field,
       the node budget). A path is refuted when both ends are closed and
       share no object: then no execution's size store on that path writes
       the holder's field, since every write of the walked fields is named
       (the standing naming assumption) and distinct sites or offsets are
       distinct addresses. A path with any OPEN reason stays relevant,
       printed with every reason. The premise is proven only when every
       relevant path gives one T: each path is tagged with its own
       element type, and the premise reports the set of them over the
       relevant paths, OPEN-UNPROVEN when it has more than one member (not
       the first path's T against the others: the verdict does not depend
       on the order paths are found, Fable 2026-10-19); with every path
       refuted it stays open (no init of the holder's table by name). Refuted paths are listed
       with their objects. The chain is
       printed as the IR has it: casts are stripped, every GEP step is
       kept, including all-zero-index ones. On every path the length is
       a constant equal to sizeof(T(newfunc)),
       with newfunc a function whose element struct is T, and all paths
       give one T. A non-constant length, a non-function newfunc, an
       address-taken or uncalled function on the way, several structs in
       one constructor or across paths: OPEN-UNPROVEN, printed per path
       (table steps, length, newfunc). The holder is then listed but not
       used: no move, one object, the copies' lengths unknown.
     - The rule report has one row per candidate: "snapshot holder of
       <owner struct> (the table its handle saves read): H <alloc>;
       handle save <locs>; element saves <locs>; restores <locs>; premise
       PROVEN, element struct T: <paths>" or "OPEN-UNPROVEN (<first
       open path>): <paths>", then "holder's entsize field at <objects>;
       n paths refuted by object identity" and one "[REFUTED <path>,
       entsize field at <objects>]" each, or "snapshot holder candidate
       <alloc>: no holder (<the first use or check that fails>)".
     - Statement: the handle image holds, slot by slot, every value the
       owner's handle array held at any save, and the element image
       every value an element of the owner held at any save. A restore
       writes into the handle array, and into each element, a subset of
       that. Every write into the block is a save from this owner, so a
       restore moves only the owner's content within the owner: the
       closure O1 checks holds through it.
     - Unknown by design: a save whose source is no element of the owner
       by name (an unkeyed cursor read: nm-O0's 4382, whose read of
       u.i.link admits the unknown-tag def/undef stores); any other use
       of the block; a length or offset that is not one value by name; a
       use of an entry reclaimed after the save (objalloc_free_block;
       undefined behavior, not modeled).
     - Unreachable by name (Fable 2026-10-19, (b); the known bits of
       plan 3.51(3), applied to a guard instead of a tag). The guard: the
       nearest conditional branch dominating H's allocation (the IR's
       dominator tree; the edge into H's side dominates the allocation and,
       checked, every save and restore of H) whose condition is icmp eq/ne 0
       of a chain of and-by-constant, lshr-by-constant, zext and trunc
       ending at the load of a named word W, and whose edge requires a
       nonzero mask (composed through the chain); any other operand is no
       guard. Checked, not assumed: (1) every object of W's address (the
       object-identity walk above) is a zeroing allocation: calloc, or a
       call to a function every non-null result of which is a call
       memset to 0 over that call's size argument on every path to the
       return (a null edge of the result exempts its path); an OPEN reason
       or any other object declines; (2) every store of W's key keeps the
       mask from the same word (or(and(load of W at the store's address,
       C covering the mask), Y), Y's mask bits known zero) or clears it
       (every mask bit known zero, LLVM's known bits); a store of another
       width, any write named otherwise over W's bytes (a field's writes,
       above; a constant-zero memset clears), or a non-zero initializer
       slot over W declines. Then, by induction over an execution's
       writes, the mask bits of every such word stay zero, the guard's edge
       is never taken, and H's code never runs: its restores move nothing.
       O1 excludes them with one ASSUMPTION per restore ("unreachable by
       name: restore <loc>: guard <loc> (mask 0x<m> of <W>), n named stores
       each keeping or clearing it (k keep; clears: <locs>), objects
       zero-allocated at <sites>"); the mask is printed, not a macro name.
       (r1, Fable 2026-10-19 (ii)) An object in which W lies only past
       every size the object can have is no object of W (an access past
       an object is in another): dropped before (1) and listed
       with the size's source: a global's or a local's type; malloc's
       argument, calloc's product; for a zeroing wrapper, the argument its
       memset 0 covers (the size it clears is the size it asked for); an
       argument is a constant, or a formal of a function never address-taken
       resolved to its direct callers' constant actuals (the largest). An
       object of no such size is kept. (r2) A zeroing wrapper whose
       allocation is a certified pool's carve is a zeroing allocation at
       its call site, resting on the pool's certificate: one ASSUMPTION
       per such object ("pool <P>: <wrapper> at <site> is an object of its
       own, zeroed by its callee (a carve of the certified pool; Carves.cc:
       <verdict>)"). A refused pool's carve declines (1) as OPEN.
       (s1, Fable 2026-10-19) A certified pool's carve is as long as its
       length (CarveSize: the form's n times its scale; a header carve
       malloc(HDR + n) at HDR is n), and that length counts only when it is
       a constant or the size formal rounded up to the pool's alignment A,
       (x + A-1) & -A with the constants summing to A-1 (-O0 keeps them as
       two steps) and A from the mask, through -O0 slots and integer
       casts. A slot whose round-up reads the slot itself is the least
       fixpoint of S = values + R(S), R the round-up (monotone,
       idempotent, R(x) >= x): R(max values). An object at a wrapper's call
       site has every return of the wrapper sized this way (a certified
       carve, a malloc, another such wrapper with its formals bound to the
       actuals), the formals bound to the call's actuals (constants, or a
       formal of a non-address-taken function resolved to its direct
       callers' actuals, the largest); a carve reached directly binds its
       function's formals to their direct callers' actuals. The object is
       dropped as r1 drops one ("its size argument (n, rounded to A)
       through <wrapper>; pool <P> (Carves.cc: <verdict>)", or "(max of k
       direct actuals: n, rounded to A)"). Any other length (a product, a
       refused pool's carve, an address-taken formal) leaves the object
       unsized: kept and listed ("kept, its size unknown: <obj>: <the
       failed condition>; wrapper <W>; pool <P> (...)"). Every reason the
       word's objects are open is logged, not only the first.
       A guard that fails a check prints "guard ...: not unreachable by
       name (<the first check that fails>)". The candidate is still
       reported; the graph is not pruned (dead-branch pruning is a separate
       lever).
       (R1, Fable 2026-10-19) Writes with no named slot (a store or a
       memory intrinsic whose destination no struct access names; a store
       straight into an -O0 local names the local itself) are not assumed
       away: each is decided by its destination's origins (the by-name
       origin walk of O1, originsOf), as writing any byte of each origin
       object. For the guard word (check (2)), W's objects are a closed
       set (every object the word can lie in): an origin allocation, local
       or global reaches W's bytes only if it is one of W's objects; an
       element origin reaches them if the container's element struct is,
       embeds or is embedded with W's struct (StructInfo::containers). For
       a field the object walk reads (its cover, above), a local or global
       reaches the field when its declared type holds the field's struct,
       an element as for W, and an allocation with no declared type is
       OPEN ("an unnamed-destination write over K: origins include an
       untyped allocation (<fn> at <site>), not typed"). Open origins are
       OPEN in both. A write that reaches or is OPEN is a write named
       otherwise (one reason per key, every such write listed once in IR
       order with its keys); a write that closes away is counted
       ("cover K: N unnamed-destination writes: a close, b reach, c open
       (z constant-zero memsets, null)"); a constant-zero memset writes
       null. The origin walks count the indirect call sites they follow
       apart ("cover: N indirect call sites through closed code fields
       followed"; distinct sites, not visits).
       (Check (2) by offset, Fable 2026-10-20) An unnamed-destination
       write whose origins include one of the word's objects does not
       reach the word when its destination's object walk (objsOf, with
       offsets) is closed and, in each of the word's objects, the bytes it
       writes are disjoint from the word's; a write whose object walk is
       open keeps the origins verdict. The walk carries offsets from the
       object's start through constant steps, joins, -O0 locals, formals
       and field loads, so a write with a runtime step on its chain opens
       it and keeps the origins verdict (nm-O0, measured: 542 of the 1846
       unnamed-destination writes have a runtime step); a chain with no
       named field on it is decided by the same walk (1304 constant
       chains, 1205 of them with no named struct step on some path,
       measured). Each such write is logged ("check (2) by offset: <loc>:
       offsets +a, +b miss the word; walk open: <first reason>", or "walk
       closed: does not reach", or "hit the word") with a count ("n of m
       REACH writes closed"). Check (2) is run against the word's kept
       objects whenever it has kept objects, also after an earlier step
       declined, and logged ("check (2) on the word (N kept objects'
       sites): a close / b reach / c open; first reason: ..."); it decides
       only when nothing declined before it. nm-O0: 1478 / 6 / 363, first
       reason display_rel_file nm.c:1170; 0 of 6 closed by offset (their
       offsets, +160/+800, +168/+816, +0, all miss the word at +3212, but
       each walk carries the word's own open reasons, elflink.c:5234 and
       display_rel_file). Cases: t_cells_container_snapshot_offset{miss,
       hit,open}.c.
       (H, Fable 2026-10-19) A recognized snapshot holder's block H
       carries exactly the structs of its saves' sources (the handle
       array's pointer range, and element bytes of the paired entsize),
       because the recognition checks that every use of H is one of its
       saves or restores (the use walk over H, its -O0 slots and joins,
       and the saves' sources by name: a handle array of one owner, that
       owner's elements); a block with any other use is not a holder and
       stays an untyped allocation. So, in that holder's covers, an
       origin that is H reaches a field only as an element does.
       (R2, Fable 2026-10-20) Copies that add nothing. (i) A block copy
       over a walked field K whose source is read under a name that puts
       the same key K at the same place in the copy (every overlap of K
       whole; e.g. section_hash_entry and bfd_link_hash_entry both begin
       with a bfd_hash_entry root) brings K's own values: a cycle. It
       rests on the name premise: every write named otherwise over K is
       counted by name program-wide (and every write with no named slot
       by its origins, R1), so the source object needs no condition of
       its own; a source under another name, or none, keeps K open. (ii')
       A save and a restore of a recognized holder are paired when their
       base and size are the same SSA value or loads of a -O0 slot whose
       stores, excluding stores of constant 0 into the size slot (a copy
       of zero bytes writes nothing) and of null into the base slot (null
       names no object), are exactly one; otherwise the restore stays
       OPEN ("ranges not paired (<the slot>: N stores[, a cursor])"). The
       pairing is path-insensitive: the save's and the restore's common
       guard is not used. A paired restore gives back what its save read,
       under the same name: a cycle in the walk, in the covers and in the
       array walk. Each restore's outcome is logged. The recognition
       already requires every handle copy's length to be one value (an
       -O0 local's entry-block 0 and one dominating store), so a size
       mismatch on a handle restore is no holder before any pairing. An
       element restore copies from a cursor (old_ent advanced by the
       entsize after each copy) and is never paired: cursor
       correspondence (both loops walk the same table in the same order
       with the same stride) is the open lever, not proposed. The
       recognition lists element restores as restores because they copy
       out of H's element region with the owner's size field as length;
       it does not match a restore to the save it returns, so H typing's
       premise (every use of H is a save or a restore) does not depend on
       that match.
     - Cases: test/t_cells_container_snapshot_{holder,other_offset,
       foreign_save,two_types,identity,initializer,nullwrite,cover}.c
       (identity: a path refuted by another allocation site, one by
       another offset of the holder's allocation; initializer: the
       holder's field initialized to a static table and stored a heap one,
       both relevant; nullwrite: a constant-zero memset over the field,
       listed, the refutation holds; cover: a block copy over the field,
       OPEN, nothing refuted); t_cells_container_snapshot_{unreachable,
       setbit,memcpy,malloc}.c (unreachable by name, and its three
       declines); t_cells_container_snapshot_{s1,s1control}.c (a sized
       non-zeroing carve through bfd_alloc dropped; a length twice the
       formal kept, unsized, with the failed condition);
       t_cells_container_snapshot_{handlearray,handlearraynull,
       handlearraygrow}.c (a hash entry reached through table[_index] and
       the newfunc call; null stored into the handle and passed to a call
       is no array; a new table through two -O0 slots);
       t_cells_container_snapshot_{unnamedcover,unnamedcoverctl,
       holderextra}.c (R1: a copy through a loaded void pointer onto the
       word's object declines; the same pointer holding another block is
       counted, not a reason; a block with one more store is no holder);
       t_cells_container_snapshot_{ktok,pairbase,pairtwo,pairmismatch}.c
       (R2: a copy into the owner from a struct sharing its root adds
       nothing and the guard holds; a base slot with two stores leaves the
       handle restore unpaired and the array open; a size slot with two
       real stores, and a restore of another size value, are no holder);
       memcpy and cover copy from bytes and from another struct name (R2's
       controls); handlearray's handle restore pairs ((ii')).
   - Tag-write values by their known bits (plan 3.51 (3), Fable
     2026-10-16): a value the evaluator cannot evaluate by its operands
     (a call's result, a load it does not follow) is the set LLVM's
     computeKnownBits allows: the known ones fixed, every bit not known
     zero or one free; used only when something is known (else the write
     is unevaluable, as before). A bitfield store beside the tag
     (elflink.c:5250's `h->root.non_ir_ref_dynamic = x`, `(old & -513) |
     ((x & 1) << 9)`) is then the old tag with bit 9 free: a write that
     changes other bits only, under the stability rule. A superset of the
     value's executions (known bits are sound), so no write is narrowed
     below what it can store.
   - The object of an access is the one its name belongs to (Fable
     2026-10-16, the identity principle of the owner code, S1-S6): a field
     inside an anonymous struct or union is named by the enclosing named
     struct and offset (accessSlot), and its object identity steps through
     the same anonymous GEPs (constant, leading index 0) to the base of
     that struct's GEP, by the same walk (enclosingNamed, one helper), then
     outward through embed-only structs as any field's. Before, the object
     was the anonymous member's address (&h->u), never the object a tag
     store on h names, so a writer of u.i.link never co-wrote type and the
     pair (bfd_link_hash_entry+40, +24) never formed. "Same object, same
     function" is unchanged: the object now matches the name.
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
     assumption is sound. The assumptions reported are the ones an answer
     rests on, the tagged pairs' (the solver checks them); a tuple a walk
     made whose result no pair took (a walk for a read left unkeyed, a
     stability check that dropped its test, a round of an effect before
     it settled) is no assumption of anything and is counted apart, not
     reported (Fable 2026-10-19).
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
     - The fixpoint is unique (Fable 2026-10-19). An effect is (maps, a
       set of terms kept sorted and unique; open, a flag; assumes, a
       set). The transfer of a callee's effect into a caller's composes
       each of the caller's prefix terms with each of the callee's terms
       (composeT) and pushes the results, ORs open, and unions the
       assumes: joins only, nothing removed, so it is monotone in the
       callee effects; the cut at more than 256 maps opens the effect
       only as maps grow, monotone too. Terms are bounded masks and
       filter indices, so the lattice is finite. The worklist starts
       every effect at the bottom (no maps, closed, no assumes) and
       re-queues a key's readers on every change until none changes, so
       it reaches the least fixpoint whatever the order. Readers are
       re-queued in IR order (module, function, argument, field), so the
       history, and every tuple a round makes, is the same in every run.
     - The one step not shown monotone: a loop inside one walk (before())
       is iterated to its own fixpoint and cut at 8 rounds, the effect
       then open ("a loop that does not settle at <loc>"). How many rounds
       a loop needs is not shown monotone in its inputs, so a cut could
       open an effect that a larger input would close. So is a pair's
       content effects, iterated as rounds and cut at 12 (every effect
       then open). Every cut is counted and listed in the TaggedFields
       line (the field, and the function and loop for a walk's). nm-O0 and
       nm-O3: 0 cuts.
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

A copy with an any-offset side (Fable 2026-10-17, a soundness fix): when
one side's cell is an any-offset cell (an unlabeled object's bytes, or a
labeled object reached at an unknown offset), the walk above does not run;
that cell meets every cell of the other side's range instead: [off, off +
L) of the other side's object (L the copy's length; unknown, the region's
extent as the walk takes it; the any-offset cell of an unlabeled object),
the write side when the any-offset cell is the source, the read side when
it is the destination. The any-offset cell itself reads and writes all its
object's cells (linkAny), so every byte of both ranges meets every byte of
the other: sound. Before, the any-offset cell met only the other side's
cell at the copy's start, and the rest of the range was lost: a struct
copied into a byte buffer at a runtime offset and back kept only its first
field (t_cells_bytecopy_any_range_a.c / _b.c: t.b() had no target).

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
  The size is a term (ruling B, Fable 2026-10-13): a primitive
  allocator's size operand(s) by its signature (malloc 0, calloc 0 x 1,
  realloc 1, reallocarray 1 x 2, aligned_alloc/memalign 1, the kernel
  family by its declared size index); a fresh wrapper's, the term of the
  allocation it returns (a constant times up to two of its formals, and
  possibly a further unknown factor: still a multiple of the known ones),
  composed through the inner call and evaluated at the call site. Never
  the call's integer arguments by position (`new_stmt(cstate, code)`: an
  opcode is no size). A wrapper whose term is unknown (a summary row
  without a body or a SIZE, a carve whose size operand has no form
  shape, return sources with no common factor) has an unknown size: one
  T, then unknown data. Counted ("fresh wrappers with an unknown size
  term").
  Term grammar (row 1, Fable 2026-10-13): add + c x formals (up to two),
  possibly rounded up to a power of two (`(n + 7) & -8`; folded when n
  is constant at the call: newchunk(cs, sizeof *p) is sizeof *p rounded
  up), and the partial factor. Partial means exactly: the size is a
  MULTIPLE of c x formals and nothing more. It decides array-or-not for
  an element whose size is c or a divisor of c, and never yields a
  count, a header, or a tail position. `x & -a` with x not exact, a sum
  of two products, and two returns whose terms differ keep only that
  fact: a multiple of the gcd of what each is a multiple of (gcd 1:
  unknown). A self call's term is F's own at its arguments, assumed and
  checked against the other returns until it holds.
  The zero case (Fable 2026-10-13, that shape only): a slot whose two
  reaching stores are a formal and a constant k, the constant's stored
  under a branch on that formal compared equal to 0 (`if (!n) n = 1`;
  -O2 `umax(n, 1)`, the same function; -O3 `select (n == 0), K, round(n)`
  with K a multiple of the rounding), is "the formal, k when zero". At a
  call it reads k for a zero constant and the actual when the actual is
  known nonzero (a nonzero constant, or a term already reading k > 0 when
  zero, scaled up or rounded); a bare formal of the caller carries it
  up; any other actual keeps only the gcd fact. Exact identities, no
  approximation: a known-nonzero value is unchanged by the zero case,
  and `(y + a - 1) & -a` over y already rounded to a is y (read from the
  sum's own operand). A header carve of `malloc(HDR + n)` at HDR is n
  (the sum's operand). binutils: bfd_alloc, bfd_zalloc,
  bfd_hash_allocate and _objalloc_alloc are round8(n, 1 when zero), exact
  at constant sizes. Through a product actual (row (2), Fable 2026-10-13):
  a zero-guarded wrapper term applied to an argument that is itself a
  term t gives "t, k when zero"; rounding to a of c x n folds exactly when
  a divides c (round8(72 n) = 72 n). The zero case names no element (k
  bytes, zero elements; an access past them is a forged pointer, rule
  (a)), so bfd_alloc2(abfd, n, 72) is an array of coff_symbol_struct with
  no tail; at the site a product of the caller's own formals is a
  multiple of c. Counted ("sized by a product through a zero-guarded
  wrapper"), split by the extent the site gets: an array when c is the
  label's size, one then unknown when c is a multiple of no label's size
  (on nm-O3 these are header-plus-data sizes whose factor is 8, such as
  elf.c:4549's sizeof (T) - 8 + k x 8, which -O3 folds to (k + 9) x 8).
  The gcd fact stays for returns that genuinely disagree.
  A pool carve's size (rule 3) by its form: before-bump, the bump n;
  counter, the decrement; minus-len, the length; header, the chunk
  call's size minus the header offset (each n times its GEP's element
  size). A carve whose size operand is not one of those shapes (a
  first piece of a fresh chunk that stays in the free space, a bump
  that differs between stores) is unknown, counted ("pool carves with
  an unknown size term"; per pool on the PoolCarve line). A row may
  declare its size (SIZE(argN), func_summaries.txt) where its body
  does not give it; the premise is the row's comment (png_malloc_base:
  the user allocator hook returns a block of the requested size,
  libpng's documented contract). A slot's value reaching a load is the
  last store before it in its block, else in the nearest block up a
  chain of single predecessors, else the one store every predecessor's
  chain reaches (all the same), else, when every store to the slot is
  in the entry block, the last one there.
  A T-typed index (a variable index or walk whose GEP steps over elements
  of T; a stride that only equals sizeof T is no evidence) on the latter
  makes it an array of T (`extendToArray`). Any other variable index from
  the T, or one whose extension is refused, also reaches the trailing
  data's any-offset cell: the T is not known to be an array of one.
  Bound clause (Fable, 2026-10-13): not an index whose address lies
  inside a declared array field that ends strictly within T (Fts3Table's
  `aStmt[40]` at +112..+432 of 544 bytes): it stays in that field, and
  indexing past a declared bound is a forged pointer, rule (a), counted
  ("variable indexes into a declared array field assumed within its
  bound"). The link remains for the implicit array of T (no array holds
  the address), an array ending at T's end (a trailing or flexible array,
  `[0]`, `[1]` or any N whose end is the layout's size), and a byte index.
  Trailing-array clause (A1, Fable 2026-10-20; plan 3.51's trailing
  arrays): a T whose last member is, recursively, an array of 0 or 1
  elements of E ending at T's end (`asection *sections[1]`), allocated
  with a known constant size of sizeof(T) + k * sizeof(E), k >= 1, conforms: the
  trailing object is the array's k further elements, labeled an array of
  E at mint, and a variable index on that array running past T's end
  reaches its element cell at the same element offset (besides its own,
  as any index). An array declared longer is a field of its own: what
  follows T is a segment, labeled by its declaration or first use, as
  below. Anything else is not a trailing array: any other size, or a
  remainder that is not whole elements, leaves the trailing object as
  before. Counted ("trailing arrays (A1)").
  Trailing [1] and [0] clause (gap 2, Fable 2026-10-20): a size that is
  a multiple of sizeof(T) reads as an array of T, but two Ts break that
  reading. A T ending in a flexible array member (`E a[]`, [0] in the IR)
  has no arrays (C11 6.7.2.1p3), so the object is the header T and its
  trailing elements, never an array of T. For a T ending in an array of one
  E (the pre-C99 struct hack), both readings are legal: the data after T is
  the next T, or more elements of the array. A variable index on that
  array, on an object read as an array of T, therefore reaches every
  element offset of T that its stride lands on (folded), besides its own
  cell. Each such (allocation, step) is a premise row in the rule report
  ("P trailing [1] index on an array of T at <site> by <step>: reaches
  offsets {...} of T (both readings kept)"), counted with the FAM headers
  in "trailing [1] arrays (gap 2)".
  Segment clause (Fable, 2026-10-13): an allocation is a sequence of
  segments, the header T and then the tail,
  and rule 1 applies to the tail recursively. The tail's label is the
  site's declaration at its constant offset (1b extended: `(B *)(result
  + c)` received by a variable declared B*, or a B struct GEP written
  at c), else its first typed use at constant offset 0 in solve order;
  its extent from the known size by the extent rule (a multiple of B:
  an array; exactly B: one; B plus data: header B and a further tail).
  What follows the last labeled segment stays data (any-offset cell).
  The variable-index link reaches only that unlabeled remainder; an
  index from T landing in a labeled segment is counted as assumed within
  its bound. Unknown size (row (3), Fable 2026-10-13): the site's
  DECLARED segments still apply, as a struct-pointer receiver declares T
  at offset 0 without knowing the size (sqlite3_malloc(808) whose term
  dies at sqlite3Malloc's indirect xMalloc, then `&pWriter[1]` ->
  Fts3SegFilter, `&pFilter[1]` -> Fts3MultiSegReader); each segment's
  extent is unknown, so what follows the last declared segment stays
  unknown, raw data; an unsized tail takes no label from a first use.
  Not admitted: a label from a non-constant offset or a variable-offset
  cast. Order: with a label from first use, an index step that runs
  before the tail is typed links the then-unlabeled tail (solve order,
  like rule 1's first use; reported). This
  holds for a sized "T plus data" as for a size that says nothing. The
  link was for the unsized case only, and that was the hole:
  `s[argc - 1].fn()` on a sized carsym block resolved nothing.
  - **Implicit array.** Under a variable index, a T that is not an array
    is read as an implicit array: the result is a folded address over the
    header's fields plus the data's any-offset cell. An element step
    after it (extent sizeof T: `p[i - 1]` as a second GEP) stays in the
    element instead of leaving the T. This is the sound
    over-approximation when the extension is refused. The link and the
    step apply to the composed offset, not only to the GEP that carries
    the variable.
  - **Cases.** test/t_cells_backstep.c (a T walked by `p++`, whose
    trailing object has T's period, so the extension is refused) and
    test/t_cells_backstep2.c (the data holds another struct). The trailing object's cells merge into
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
the order dependence wherever a site declares; char and void receivers
declare nothing. Scalar clause (ruling A, Fable 2026-10-13, completing
1b): a block whose every creating site declares no struct and no pointer
and accesses it only as one scalar of 2+ bytes (float, double, int,
long, an enum; a vector's element counts as its element), with the
receiving variable's declared scalar pointee if it has one, is an array
of that scalar from mint ("float[]"); a struct step into it is rule (b),
"struct written into storage declared scalar", folded into the array's
element cells with the flow kept (an S-typed read through it reads the
write: sound, counted). Folding is sound both ways, and the only layout
read that sees the write is a pointer-typed load at a scalar element,
itself a mismatched access (Fable 2026-10-13: no raw-cell twin). A block whose every creating site uses it only
as bytes (char loads and stores, the string functions: str*, sprintf)
is marked used as bytes from mint (a mark, not a label; bytes is not a
label), so a struct written later is the existing row "struct written
into storage used as bytes". memcpy/memmove destinations are not byte
uses, and the list must not be "completed" with them: rule 1 lets a
fresh block take a copy source's layout (the bison YYSTYPE shape).
memset is neutral. A creating site that classes the block otherwise
gives neither (every site must agree; escapes of the pointer do not
disqualify). Struct evidence against a scalar label (A3, Fable
2026-10-21): a struct GEP on a phi or select that has the result among its
incomings (skb_ext_add: the refcount stored as an int, then skb_ext steps
on a phi with the old extension), or a receiving struct field whose debug
type points to a struct (coffcode.h:1121 at -O3: comdat = bfd_alloc(16),
->symbol stored through the result, ->name through a reload of the field,
in the IR struct the linker merged coff_comdat_info into), makes the
scalar label a conflict: the site is unlabeled, both candidates reported
(rule report "B conflict", one row per allocation in IR order). Evidence
only, never a label: the join may step on its other incomings, and the
field is a base-class slot (row 3), so over-removal costs precision, not
soundness. The merged identity (A4, Fable 2026-10-21): the IR linker
merges structurally identical structs under one name (elflink.c:9521's
symshndxbuf, an Elf_External_Sym_Shndx array, reads as rndx_ext), so a
heap object labeled by an IR struct takes the debug name of a struct
its site's own receivers declare (a variable's type or a receiving
field's pointee, through the reach below; never a use elsewhere; the
IR carries no sizeof type) when no IR struct has that name and its size
is the label's. A rename only: the layout, hence every cell's offsets
and every answer, is the IR struct's. The IR name stays, counted, when
no receiver at any site has a debug type or the sizes differ, and
stays, reported ("A4 identities", one row per allocation in IR order),
when the sites name several; neither is a label conflict, since the
layout is one. A site's own receiver (A4, A5; Fable 2026-10-21) is a
variable whose frame, its subprogram with the inlinedAt of its dbg.value
or dbg.declare, is the call's own frame or one the call was inlined into
(compared as pairs, so two inlinings of one function stay apart), or a
receiving field's pointee; a frame inlined beside the call that the value
is passed to is not (-O3 _bfd_x86_elf_link_hash_table_create: the formal
`table` of the inlined _bfd_link_hash_table_init is excluded, `ret` and
bfd_zmalloc's `ptr` count). The size readings (A5a, Fable 2026-10-21): a
constant size S = k x sizeof(L), k >= 2, with L a struct label and the
extent an array, is an array of L by rule 1, and it is also any struct C
that embeds L at offset 0 with sizeof(C) = S (the embedding table): C
inheritance whose container's size happens to be a multiple of its head's
(2088 = 29 x 72, elf_x86_link_hash_table over bfd_link_hash_table). Three
outcomes. A receiver declaring exactly one such C (its IR copies one
layout) names the object C: relabeled, one object (counted). A receiver
declaring L is in both readings and selects nothing, and no declaration
selects nothing: a conflict, the site unlabeled, every reading in the row
("A5 readings <loc>: k x L (sz) vs C1 (S) ...", one row per allocation
site in IR order, over every site, not only those a capped solve
reaches). Receivers naming several Cs: a conflict too. Never kept as an
array of L when a C reads it: picking either reading unchecked misnames
the other's cells; unlabeled, the object's cells are bytes, which costs
precision, not soundness. The cache sizes (A5b, Fable 2026-10-21): a
kmem_cache_alloc, kmem_cache_zalloc or kmem_cache_alloc_node object is one
object of its cache's size, when the cache argument is a load of a global
whose only write (null initializer; every other use a load) stores a
kmem_cache_create or kmem_cache_create_usercopy call with a constant
nonzero size, and the global is internal or the run whole-program (then
the write is looked for in every module's copy of the name); otherwise
refused, the reason counted and the site listed. One object, never an
array (a slab hands out one object per call): the label itself when its
size is the cache's; else the one struct of the cache's size embedding the
label at offset 0 names it (-O2 kernel do_timer_create: list_head, the
first member its init writes, in @posix_timers_cache of 256 bytes, is
struct k_itimer); several such structs, or none: a conflict, unlabeled,
its row. A site with no mint label keeps its size term (rows "no mint
label", for the census-only names to come); a declared array (a scalar's)
is kept. The size label and A5a's readings do not apply to a sized cache
object. The mint table that holds these decisions (05ed76b; the solve's
only source since A5a) is rebuilt before every solve iteration: a later
iteration marks allocation sites the first did not, at indirect calls the
previous solve resolved to an allocator (cjpeg jinit_read_gif rdgif.c:707
-> alloc_small), and a table built once would have no entry for them. The site's reach (row 3, Fable 2026-10-13): the receiving
declaration is a variable's or a struct field's (`opt_state->space =
malloc(..)`: the field's declared member type, through nested members; a
store to a struct global or local itself is its member at offset 0), a
field's only for a scalar or pointer-slot pointee: a struct-pointer field
is a base-class slot (libjpeg `cinfo->dest`, declared
jpeg_destination_mgr *, receives a my_destination_mgr; taking it made
cjpeg-O3 run out of memory), so its pointee declares nothing (a
base-class slot: the block falls to other creating sites' declarations
or its first typed use; counted in the rule report, "SUMMARY sites"). The
result's uses are followed through a slot stored once, and through a
cursor slot: every other store into it is a reload of it stepped by a GEP
(`*ep++ = d`; `p += nodewords`, a variable step, inbounds in the block),
the forward-only cursor the pool recognizer names; the cursor's reloads
classify the block (no offsets, no labels from them). A variable step is
admitted because the census needs only the kinds of the uses, never their
positions, and the mark changes where a later write lands, not whether. A slot that also
holds another value (a call result, a foreign load; a null store is no other block: binutils
_bfd_pei_swap_sym_in's `name` holds _bfd_coff_internal_syment_name's
result, then the bfd_alloc) leaves the site unclassified, counted: it
gives no bytes mark (followed uses are what give it). The receiver's
KIND is its declaration, the variable's or field's debug type, whatever
else its slot holds (Fable 2026-10-13): a slot that also holds another
allocation, a load, a call result or a formal still declares its kind
(struct, pointer slots, scalar) for every fresh block stored into it;
its uses are followed only under the single-store or cursor condition.
Sound as ruling A: the declaration is what the program wrote for the
variable; a block too small or large for it is the extent rule's
business. Counted (SUMMARY sites): "declared through a shared slot" and
"with no declaration" (the genuinely kindless). A site with no receiving
variable (its result returned or passed straight to a call) declares
nothing; counted (census line: "with no receiving variable"). Following
the result into the callee's formal (part 3) is not built: by the per-site
rule such sites are rarely heavy (Fable 2026-10-13). A declared scalar array takes no extent
rule: its element label already names every element, and the extent rule
can only cut a tail, which a scalar array has none of. The same holds
for a pointer-slot array declared at mint (1b's T** receiver): its label
names every slot, it takes no extent rule, and a mismatched struct write
folds into slot cells with the flow kept (Fable 2026-10-13). The third
form, a struct (Fable 2026-10-13, sqlite3's OP_Program frame): a declared
segment of struct T that the site also indexes by a variable index of T
(`pEnd = &VdbeFrameMem(pFrame)[n]`; not a carve, whose result is used as
another type, and not a constant step, `(C *)&b[1]` being the next
segment's start) is an array of T without an extent: every element
named by T's field cells, no tail. Data after it at a variable offset
(`p->apCsr = (VdbeCursor **)&aMem[nMem]`, a field receiver, so no carve)
reaches it by another stride, which folds into T's element cells at
every offset the stride reaches (rule (b), flow kept; counted "struct
array followed by other data at a variable offset"). Sound as the other
two: the label names every element, and a mismatched stride lands in the
element cells it can touch. Receiver kinds apply to every declared
segment as to the result (Fable 2026-10-13, sqlite3's jsonParseCached):
an address `p + c` (c > 0) received by a variable or a struct field
declares the segment at c by the receiver's kind: a struct (a variable
only; a struct-pointer field is row 3's base-class slot), an array of
pointer slots (T **), of a declared scalar, or byte storage (char *:
`p->zJson = (char *)&p[1]`, used as bytes from mint, inert: a mark, not
a label). Counted by kind ("SUMMARY segments declared by a receiver").
A result slot that also holds other values is followed for SEGMENTS only
through its reloads that the site's store alone reaches (pFrame,
assigned four ways in sqlite3VdbeExec; the reloads after the allocation
are the block): such a reload holds exactly the result, as a single-store
slot's reloads do; the site stays unclassified for its scalar and bytes
marks. Counted (SUMMARY sites). Uses inside a callee the
block is passed to are not followed (part 3, callee formals: not built;
neither example needed it). Neither part has a soundness premise: the label or mark
changes which cell a later struct write lands in, never whether it
lands, so a block created as scalars or bytes and later used as a
struct through an escape is a counted row instead of a label. Kernel
note: `unsigned long storage[]` used as aligned struct storage becomes a
rule (b) row through the element cells, less precise than a first use
and sound; acceptable, counted. Kernel dispatch (Fable 2026-10-13): a
static_call trampoline is a load of its key's func cell. A direct call
to a bodiless `__SCT__X` is an indirect call whose callee is the content
of (@__SCK__X, static_call_key.func); the trampoline is never an origin;
the key's initializer and `__static_call_update`'s store `key->func =
func` (a body in the corpus) are ordinary flow. Premise, per site:
"trampoline __SCT__X dispatches through __SCK__X.func". A trampoline
without a visible key stays an extern call (outside), counted.
`__traceiter_X` is a defined function, called directly; its dispatch
over tp->funcs resolves by flow (one allocation pool for every
tracepoint's probe array: an allocation-site confluence, not modeled
away). A later incompatible use (a struct
written into storage used as bytes, or into an allocation laid out as
another struct) is reported as rule (b), not admitted as a layout. The
other order needs no row: a byte access on a labeled object runs over its
fields (the any-offset cell). The order dependence is the old model's
(bytes, then struct, was never labeled). Containers at offset 0 (row 2,
Fable 2026-10-13): a struct step naming S at the start of an object
labeled T, where S has T at offset 0 and the allocation's known constant
size fits S, widens the label to S, the extent by the size against S.
Only a T followed by data whose trailing object is not yet used: inside T
the folded offsets are the same under S, so every existing cell keeps
its meaning, and its name (cell names inside T stay T's leaf names; new
cells past T are S's). Refused, counted by reason: an unknown or
non-constant size, a size S does not fit, an array of T (its folded
element addresses would change meaning), one T exactly, a used trailing
object; such a step stays a rule (b) row.

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
- A formal returned unchanged (bfd_hash_newfunc's `if (entry == NULL)
  entry = alloc (...); return entry;`, Fable 2026-10-17) is the realloc
  shape inferred: when a fresh source also returns, the wrapper is FRESH
  ALIAS(ret=arg_i) BODY (logged "[fresh-or-arg]"); a formal and no fresh
  source, or several formals, reject it (R1). Null reaching the formal is
  the fresh path, as for realloc(NULL, n).
- What reaches an inherited ALIAS's argument may also be a fresh object of
  the wrapper's own: a certified pool's carve, or a call of an allocator
  whose summary is FRESH alone (or one assumed in the same round). The
  wrapper's own FRESH names it per call site already, so it is covered
  (the derived newfuncs pass their own block to bfd_hash_newfunc).
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

Init atoms carry their offsets (Fable 2026-10-14). An alloc-init
wrapper's atoms ST(*ret <- argI), ST(*ret <- @g), the self-store and
FreshSub were built at offset 0. Under cells, an allocator called inside
a kept allocator body has no object (the outer FRESH stands for it), so
the body's own stores write nothing and the atoms are the stores' only
effect: `c->ops = g` landed in the object's first cell and a read of
`c->ops` found nothing.
- **Statement:** an init atom carries the byte offset of its store from
  the fresh pointer (casts and constant GEPs accumulated); unknown
  offsets (a variable index, a negative offset) are a write of unknown
  extent. A composed init helper's offsets are from its object
  parameter, and compose by adding the offset of that parameter inside
  the fresh object. A self-store also carries the offset of the interior
  address it stores. (Cells runs a field-sensitive graph, 13 buckets set
  by --cfl-cells, so both offsets take exact field edges. Flows-to applies
  a summary atom's offsets only under field buckets, --cfl-field-buckets
  > 0, as --cfl-nexus-fields sets; with 0 buckets, the default "full",
  "base" and "pexact" configurations, every atom reads and writes its
  base cell and the offsets are inert.)
- **Integer carriers:** a pointer-width integer stored through the fresh
  pointer that graph build treats as a carrier (its int-store rule:
  ptrtoint upstream, an integer formal, a load or a call) moves a
  pointer. A constant ptrtoint is classified as its pointer (a global);
  a ptrtoint instruction is already a side effect that refuses the
  wrapper (R3). Any other carrier is classified by its sources, followed
  through casts, arithmetic, joins and spill-slot reloads: a formal is
  an argument atom (cflow's depmap_alloc stores `count` and a size
  computed from it: ST(*ret<-arg0) ST(*ret@8<-arg0)), a ptrtoint
  constant a global atom, a plain constant no source; a load from
  memory or a call refuses the wrapper, as a stored loaded pointer does
  (`init-int-carrier`). Helpers follow the same rule, and a
  helper's integer-carrier store outside its object is a side effect
  that rejects it.

Cases: test/t_cells_freshinit.c (a global at +16, a helper's formal at
+40 through the helper's object at +32, a stored loaded pointer refused),
test/t_cells_freshinit_int.c (constant ptrtoint stores) and
test/t_cells_freshinit_intarg.c (an integer formal, its -O0 reload).

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

**Carve sizes (A2', Fable 2026-10-20).** A carve's size term is exact IR
arithmetic, or unknown:
- Before-bump: the bump n of `store H, p + n`, one value for every bump
  store of H in the function. Two bumps read as the piecewise term
  "x, K when x == 0" only when the constant bump K sits on blocks
  dominated by the true edge of `x == 0` and the variable bump x on none
  of them (-O3 bfd_alloc: x = `select (n == 0), 8, round8(n)`); any other
  mix stays unknown.
- Header: n for `malloc(HDR + n) + HDR`. A header carve c followed by the
  store `H := c + x` into its pool's bump field is a piece of x: the rest
  of the chunk is the later carves' space (a store `H := chunk + off2`
  is the constant piece `off2 - HDR`). "chunk - HDR" remains only for a
  header carve with no such store.
- A join that is itself a certified carve (the return phi of an inlined
  objalloc_alloc) reads its own carve term joined with its incoming
  carves' terms; an incoming load of the pool's fields is the
  before-bump result. This reading rests on the certification's "the
  before-bump result is a load of H". An incoming constant carve on the
  true edge of `x == 0`, x the join's bump, is x's zero case: it joins
  when the term reads that constant there, the zero case's value after
  the term's rounding (round_al(zeroK) for an aligned term: -O3
  bfd_hash_allocate is round8(n ? n : 1), whose zero case reads 8). Equal
  terms give that term, others the gcd fact; only a constant labels.
  Count-times-size with an overflow check (bfd_alloc2, bfd_zalloc2) is not
  a form: unknown, counted.
Counted: "size terms (A2'): a carves by "n, K when n == 0", b carve phis
by their carve term, c header carves by the store H := c + n, d zext masks
read as -al; e fresh functions still unknown".
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

**Post-solve check of the handle cells.** After the solve, every store or
block copy (memcpy, memmove) whose pointer may reach a certified pool's
handle cell, other than the pool's own typed accesses classified before
the solve, is a rule row:

> the solver's facts admit a writer of this handle cell outside the pool's
> forms (site); the carve model assumes that write does not change the
> handle; sound when the program keeps its pool discipline; first cause:
> the imprecise pointer at (site)

- The first cause is the leak census's tag on the reaching fact at the
  writer's pointer, under --cfl-cell-leak-census.
- These rows are a class-7 leak into the handle (a store through an
  imprecise pointer), not a new rule class. They fall with the soup and
  are tracked in the per-program state like the other counts.
- The rows check the third hypothesis (a handle reached only through
  typed accesses) as far as the solver's facts allow. The certificate is
  kept where rows exist: they come from the solver's imprecision (soup
  pointers holding the pool descriptor), not from program writes. Under
  the certificate a handle load has no data use, so anything that lands
  in a handle cell never flows into program data.
- Counts at 2026-10-12, run at the cells gate's 200K stop for nm-new:
  - tcpdump O0/O3: 0;
  - nm-new O3: 0;
  - nm-new O0: 358 with handle stores modeled; 0 once they are not (see
    below). All 358 had their first cause at the bump or the rewind
    through the imprecise `o`.

**Handle stores are not modeled.** A certified pool's handle values are
not data: cursor reloads, free-space pointers, chunk pointers, rewind
values.
- **Why.** The chunk's contents are reached only through carve results,
  which are fresh objects, and its header fields hold only handles. So a
  handle value leads to no cell that can hold a function or a data
  pointer of the program.
- **So.** A store whose stored value is a handle value adds nothing a
  consumer can read, whatever its destination, and is not modeled. That
  covers the bump, rewinds, refills into handle fields, `chunk->next =
  o->chunks` and `o->chunks = chunk`.
- **The destination does not matter.** The argument is about the value,
  not about where it lands: a store through an imprecise descriptor
  pointer (binutils' `o`, loaded from abfd->memory) is covered without
  asserting that the pointer is precise.
- **Hypothesis:** the certificate. Stores of other values into handle
  fields stay modeled (under the certificate there are none, and the
  post-solve check reports any the solve admits).
- **Counts per pool** are in the PoolCarve report ("N handle stores …
  not modeled"): nm-new objalloc 23 (O0) and 146 (O3); tcpdump newchunk 2 (O0) and 309 (O3, inlined).

**Confirmer.** A carve result is a fresh source for R1. The certified
pools' bookkeeping (handle-field stores, the bump, rewinds, ptrtoint of
handles) is exempt from R2 and R3, because it is the pool's own state
that the checks cover. bfd_alloc and bfd_hash_allocate are then
confirmed, and so is _objalloc_alloc (greatest fixpoint); their hand
rows are removed.

**The confirmer and the solver read the same certificate** (plan 3.55
(a), Fable 2026-10-13). A pool's constructor stores into the handle fields
of the block it returns: `ret->chunks = malloc(..); chunk = ret->chunks;
ret->current_ptr = (char *)chunk + HDR` (objalloc_create). A store into a
CERTIFIED pool's handle field of a value derived from THAT pool's chunk
(a read of one of its handle fields, through casts, address steps and
spill slots) is the pool's own bookkeeping, not an escape or an
untraced init; so is a read of such a handle field of the fresh block
whose every use stays in the pool (compares, writes into the pool's
handle fields through it, stores of it into them). Bound to the
certificate: only where PoolCarve certifies both the handle field and
the chunk's fields as one pool (objalloc+0/+16 with objalloc_chunk+0/+8);
any other field, or a value from elsewhere, stays an escape. It is the
same statement the solver uses not to model handle stores: a handle value
leads to no cell that holds program data. Counted ("handle-field reads
and stores exempted by a pool certificate", ConfirmFresh line).

Not mechanized. Checked by executions; see the rule 3 commit's gates.

## Container storage closure (Containers.cc, --cfl-container-closure, 2026-10-13, plan 3.55 deliverable 1)

A container's storage is a block its owner object holds in a field K
(bfd_hash_table+0, the bucket array; sqlite3's FuncDefHash). Today a cell
of such storage is (allocation site, k): every table made at one site
shares one name, so every lookup meets every table's entries.

**Obligation 1, storage closure, is the FEED condition** (checked per
field K; Fable 2026-10-13): every store into K stores a fresh block (an
allocation, a confirmed fresh wrapper's result, a certified pool carve, a
join of those with null), null, or a re-store of K's own reload of the
SAME owner (its base pointer, or a -O0 local stored once; `old_table =
t->table; ... t->table = old_table`). `a->t = b->t` moves a block between
owners: it is another value, and it opens the field it is stored into. A
field failing the condition is open, with the other values reported (rule
report section CLOSURE).

The load side opens nothing. A pointer read from K carries the refined
name (O, C) wherever it goes, so passing it on, returning it, joining it
or storing it elsewhere is ordinary flow; the report lists where such
addresses go, as information. (A first version also opened K on those
uses; that stricter check is withdrawn.)

**Paired sites.** A fresh block's site C is owner-paired only when every
use of its result before the feed is the feed store into the closed field
or a transient use (casts, address steps, -O0 local slots, compares,
writes through it, free, a call to a pool API below). If C's result also
reaches an open field, a return, another call or a global, C keeps its
plain object, and the closed field's cell holds plain C for that site
(the field stays closed; counted "closed feeds whose site is not paired").
Without this a block leaving by the other path would have no name while
the owner pointer has no fact.

**Pool APIs** (3.55 (b), Fable 2026-10-13): the feed condition for a
pool's OWN handle fields, whose chunk list is fed inside the pool's
functions through a formal (`o->chunks = chunk` in _objalloc_alloc). A
handle value passed to a callee stays in the pool when the callee's
formal reaches only (i) one certified pool's handle fields (reads and
writes through it, as the PoolCarve certificate names them), (ii)
non-pointer fields of the descriptor (objalloc's current_space: no
pointer moves), (iii) compares, (iv) freeing the descriptor, (v) the same
check through further callees with a body (a recursive call adds no use:
greatest fixpoint). Stored elsewhere, returned, passed to a bodiless or
indirect call: not a pool API. The function set is what the check finds,
never a list of names; counted per program (nm-new 3: _objalloc_alloc,
objalloc_free, objalloc_free_block; sqlite3 0; tcpdump 0). Carves made
from a closed handle are the owner's storage: (P, carve site) with P the
pool object at the carve, itself (owner, pool site); rule 1 lays each
out, the carve form's size term as its extent.

**Statement (the model, before any census).** Closure refines a cell
(site, k) into (owner object, storage, k), per owner object. Sound
because, under obligation 1, every concrete block made at the site is
reachable from exactly one owner object's field K: it enters only by a
fresh feed (a new block, one owner) or a re-store of the same block, and
null adds none. An abstract owner object stands for its concrete owners,
so the refined name is a function of the concrete block. Pointers TO the
storage, once read from the owner's field, may flow anywhere: they carry
the refined name, which is the name of every access to that block.
- Two owner objects made at one allocation site keep one name (the
  site-confluence row; owners are as precise as the solver's objects).
- The refinement splits objects, never merges cells: no two blocks'
  cells merge that the site's single name did not already merge.

**The primitive: an owner-paired mint** (Fable 2026-10-13). For a closed
field K and a feed store `o->K = v` of a paired site C: when an owner fact
O reaches o, the object (O, C) is minted (lazily, as o's facts grow) and
added to the cell (O, K) ONLY, and to v's node, so v's transient uses
hold every (O_i, C). Plain C is never minted for a paired site. Re-stores
are ordinary stores. Sound: a concrete block of C is stored into some
owner c in the concretization of O_i and is named (O_i, C); v
over-approximates with every (O_j, C); nothing else reaches the block.
Rejected alternative, do not rebuild it: keep C and add content edges
from C to each (O, C). A read through the raw pointer after an owner's
write would miss that write (unsound), and edges both ways would merge
every owner's contents through C (no precision).

**Container rows** (plan 3.55 deliverable 1; func_summaries.txt `@container`
blocks, Containers.cc; Fable 2026-10-13/14). A row names a function's role on
the owner at OWNER(argN). Before any row is applied, the engine checks the
container; failing any obligation REJECTS it (its rows are not applied, the
bodies are solved as today).
- The body: the row functions, the functions only they call (direct
  calls, address never taken), the constants fed into a closed code field
  (below) and what only those call.
- Derivation: a value of a body function is derived from its owner o when
  loaded through o's closed handle fields, or through LINK fields (pointer
  members of the container's structs that point back into them: next, prev,
  a bucket's chain) or storage slots of a derived value; another member is
  the element's payload. A fresh block the body makes, and an insert's
  ELEM(argN), count as the owner's new elements under O3's containment.
  Across body calls a formal is derived when every body call passes a value
  derived from the same caller owner value, with the owner passed too.
  The null part of a class is ignored at a load or a store (it never
  executes).
- O1: every handle and link field is closed: every store into it is a
  fresh feed, null, a same-owner re-store, or an element moving within one
  owner (a derived, new or null value stored, in the body, into the owner
  or one of its elements). A field's feed set is computed through
  non-escaping formals, each call site's actual judged at its caller.
- O2: a lookup returns null, a derived value, a payload of one, or an
  insert row's result.
- O3: an insert's element, and every fresh block the body makes, goes only
  into the owner's storage: stores into the owner or its elements, writes
  through it, reads (a copy's source), zeroing, a body helper's or a row's
  formal (checked there), a no-op callee, returned. A block copy INTO it is
  a store of the source's fields: the source must be derived or fresh
  (per-field decomposition).
- O4: every callee outside the body is a row of the container, a carve
  row, an allocation or a free, a prover no-op, a pure row, or does not
  return. An indirect call through a closed code field calls its fed
  constants (code-field closure: every store into the field is a function
  constant, a formal fed only by constants, null or a same-owner reload; an
  aggregate copy of the owner opens it); the solver's targets at that site
  are checked to agree (post-solve). The same closure gives object
  identity's formal rule (f, Fable 2026-10-19): when every address use of
  an address-taken F is an actual to a non-address-taken init function
  that passes it down to a store into such a closed code field, F's
  callers are its direct callers and the indirect calls through that
  field (found by the graph build's own test, isIndirectCallSite, which
  runOnFunction checks against the context's indirect-call set). A pure row's own indirect calls are a
  premise checked after the solve against the solver's targets (no target,
  or each target with no pointer store, no block copy, no indirect call);
  a check made at a stop is labeled so, and no number comes from it.
- O6: every element pointer field the body reads is one the body writes.
- Sentinel element (a checked identity guard): a zero-initialized global of
  a container struct the body hands out as an element ("absent"). (s1) its
  address stays in the body: never stored to memory, never returned by a
  row, never passed out; (s2) a guard field g, a pointer zero in the
  initializer; (s3) every store (and block write) through a pointer that
  may be the sentinel is dominated by a test `p->g != null` on the same
  pointer value (the SSA value, or a reload of a slot stored once, so no
  store lies between the test and the reload); there, p is not the
  sentinel. The induction: base, the zero initializer; step, a store into
  the sentinel's g would need the sentinel's g non-null, false. (s4) a
  field is concluded null in the sentinel only when every store into it is
  in the guarded set. Loads of such fields through a may-sentinel pointer
  contribute null.

**Transfer and adoption.** At a call site OUTSIDE the body, a verified
row's transfer replaces the call's result: an insert's element flows into
the owner's element cell (O, "C.elems") for every O in pts(owner actual);
a lookup's result is that cell (plus null); the argument-to-formal wiring
stays, so the body's own side effects through the arguments (counts, the
storage stores) remain, and the body is still solved for its own callers.
The element cell is its own node, outside every content cell, so no other
access reads or writes it. Single-callsite merges (global dedup) skip row
functions: the call's result must not be the body's return. Sound given
O1-O4 and O6: nothing else can hold an element's address before a lookup
returns it except the owner's closed storage, so every element a lookup
can find was inserted through a row into that owner's cell.

**The element mint** (Fable 2026-10-13/14). An insert whose element is
its result (ELEM(ret): bfd_hash_insert; bfd_hash_lookup with CREATE)
makes the element inside the body. At such a site s outside the body,
RET is the row object (O, s, elem), one per owner object O in
pts(owner actual), minted as the owner's facts arrive. It enters the
owner's element cell (O, "C.elems") and the body's element values (the
constructor results inside the body), so the body's own reads and writes
of an element reach it. It inherits the offsets the body writes on its
own element objects (C -> row, never row -> C); a container whose body
writes an element at an unknown offset is not minted (refused, printed).
A CREATE argument that is the constant false makes the site a lookup
only.
- **Inline insert, (d):** an owner-code call to a verified container's
  constructor (a code-field target), outside the body, is an insert site
  s: its element is of the owner passed to the constructor. RET is minted
  per owner as above. An element derived from that owner value (the same
  SSA value, or the same GEP shape) re-stored into a link field of an
  element of the same owner is a same-owner re-store (O1).
  Through a closed code field (Fable 2026-10-16): a call through a code
  field whose closed set has only constructors, all paired with the owner
  at the same argument, and whose owner actual there has the shape of the
  object the field is read from (linker.c's `(*info->hash->table.newfunc)
  (NULL, &info->hash->table, name)`), is such a constructor call: its
  result is an element of that owner, for O1's same-owner pairing of
  stores and copies (`*sub = *h`). The minting already counted such calls
  as element sources (t_cells_container_ctor_field.c). A call whose owner
  actual is another object is not paired
  (t_cells_container_ctor_field_other.c). Two reads of the owner
  that are separate loads of one field (-O0's `info->hash` read twice)
  have different shapes; their identity is S6's re-read check, not this.
- **Statement:** the row object (O, s, elem) stands for every element
  made at s for an owner in O. Every such element is reachable only
  through the owner's closed storage (O1-O3) and through the result at s,
  so naming it by (O, s) loses no flow: an element of O is never an
  element of another owner, and the body's own accesses to its elements
  reach the row object through the element values.

- **Size label** (Fable 2026-10-14): a heap object whose allocation size
  is a constant S larger than its label T (the label its site's uses or
  its first typed access give) takes the label of the struct of size S
  that embeds T at offset 0, by the struct analyzer's embedding table
  (transitive). Exactly one such struct: relabeled. Several: T stays,
  counted as "ambiguous size label" with the candidates printed. None, a
  non-constant size, or T already of size S: unchanged. A multiple of T's
  size is an array of T (plan 3.53, rule 1), not a container. An
  allocator's size comes from a summary row's SIZE, else its signature
  (the allocator table), else its body's inferred term: a row's size
  position is read before the allocator table (whose kmalloc*/__kmalloc*
  prefix entry takes arg0, the cache, in kmalloc_trace(s, flags, size)).
  The kmalloc cache forms of the pinned kernels have rows: 5.18
  kmem_cache_alloc_trace / _node_trace, 6.8.2 kmalloc_trace /
  kmalloc_node_trace, 6.18.7 __kmalloc_cache_noprof / _node_noprof (the
  request, arg2 / arg3).
  The term evaluator (A2', Fable 2026-10-20) reads constants, formals,
  sums, products, shifts, casts, `x ? x : k` (select on `x == 0`, umax with
  1), `(x + al - 1) & -al` rounding, and the mask `2^k - al` in place of
  `-al` when the IR bounds the sum below 2^k (`zext_iN(y) + c` with
  `2^N - 1 + c < 2^k`; -O3 bfd_hash_allocate's `& 0x1fffffff8`). A pool
  carve's term is its form's size (see "Pool carves", A2'). Anything else
  is unknown and counted ("size terms (A2'): ... still unknown", and the
  extents' "fresh wrappers with an unknown size term").
  Worked example (5.18): snd_hda_codec_device_init allocates
  kmem_cache_alloc_trace(.., 1640) and first uses it as struct
  hdac_device (944 bytes). In the 5.18 kernel IR (2,623 modules) the only
  struct holding hdac_device by value is hda_codec, at offset 0, 1640
  bytes in all 8 modules that define it; 1640 is not a multiple of 944.
  The object is a hda_codec; before the rule its bytes past 944 were past
  hdac_device's layout, and a step as hda_codec was a name conflict.
- **Statement:** a label partitions one object's bytes into named cells;
  this rule chooses the partition the program's own sizeof declares (the
  allocation asks for the container, the code reached it first through
  its first member). It narrows no flow: every access keeps its offset,
  only the names past T's size change from bytes past the layout to the
  container's members (no type narrowing, rule untouched). The row object
  layout below uses the same rule for a constructor's element.
- **Row objects by constructor type** (Fable 2026-10-19; replaces the
  2026-10-14 "Row object layout" rule). An owner's constructors are the
  code-field feeds paired with their owner where the constant is fed (up
  the formal/formal call sites: `bfd_hash_table_init(&nbfd->section_htab,
  bfd_section_hash_newfunc)`), by the static by-name walk of the code
  field's stores; an unknown on that walk opens the code field and O4
  rejects the whole container (per-owner refusal waits for owner identity
  by name). A constructor's element is its own fresh block of constant
  size (a call, or a certified pool carve; a chunk-relative carve is the
  same request as the constant one), typed by a typed step, else a local
  variable's debug type, else the unique struct of that size that embeds
  a struct the body steps through on an element; every constructor's
  struct must embed that body struct at offset 0, or the mint is refused
  ("element size unknown"). A constructor measuring several sizes has
  each struct.
  - A row object is (owner object, owner offset, mint site, T): one per
    element struct T of a constructor fed to that owner, laid out as T,
    and the row's result and row cell point to every one of them. Two
    constructors of one T share the object (the key is the type);
    isomorphic structs stay separate (different names). A constructor
    with no struct type is its own T: one unlabeled row object with byte
    cells.
  - No layout is chosen among constructors (no largest, no common
    prefix, no container-wide fallback): two structs folded into one
    layout merge cells across names, which the design forbids, a shared
    prefix included.
  - The owner's T set grows with the facts: a fact at a feed's owner
    value adds the feed's types to each owner it holds, and mints them
    at every mint site that owner has reached; a mint mints every type
    known for its owner. A minted object keeps its layout. At a fixpoint
    the objects do not depend on the order facts arrive; at a stop they
    are partial, like any fact.
  - An owner reached by no feed has no elements: at a fixpoint no
    constructor reached it (the walk is complete, or O4 rejected the
    container), so its rows return nothing; counted ("rows of owners
    with no constructor fed: n"). No unlabeled fallback object: one
    beside every typed row would put byte cells there, the soup again.
  - An access past T's size on a T object (a step, an inherited body
    field, a block copy's bytes) names no cell of this object: it is
    another type's field. It is dropped and counted, not asserted (at a
    stop the other type's object may not be minted yet). At the end of
    the solve each such access must have found an in-range row object of
    the same owner, else it is listed as a wrong pairing, per access,
    stated, not asserted. Inherited body offsets past T are the same
    rule.
- **Statement:** every element an owner's rows can return was made by a
  constructor fed to that owner, as that constructor's struct; the row
  objects of an owner are exactly its constructors' structs, so each
  element's bytes are named by its own struct, and the answer is the
  union over the owner's constructors. The constructors' structs share
  the body's element struct at offset 0, so the body's own accesses name
  the same bytes in every element.
- **The 2026-10-14 rule's code was unsound.** It said "asserted: a write
  past its layout is a wrong pairing", and that part was right, but the
  assertion sat in tailOf, which a row object never reaches; the layout
  was fixed at the first mint from the constructors the owner's feeds
  held then (else the container's largest), and an access past it went
  to the object's outside cell. Witness: test/t_cells_container_row_late_ctor.c
  (big_newfunc reaches the owner late; e->fc() answered [] where the
  program calls ga).

Not mechanized. The census re-cut (nm-new, sqlite3; tcpdump unchanged)
measures it after the gates. Cases: test/t_cells_container_mint.c,
test/t_cells_container_poolchunk.c, test/t_cells_container_row_late_ctor.c
(and its _ctl control), test/t_cells_container_row_two_ctors.c.

**Pool chunks inside the body** (Fable 2026-10-14). O3 (containment):
every fresh block the body makes goes only into the owner's storage.
At -O3 objalloc_alloc is inlined into the constructors, so the body
makes the pool's own chunk and stores it into the pool's handle field
(objalloc.c:168 `o->chunks = chunk`). A fresh block stored, through
casts, by a handle store of a CERTIFIED pool (the same certificate as
closure (a)) is pool storage, not an element: the certificate covers
its uses, and its carves are the elements. It is exempt from element
containment and counted ("N pool chunks allocated inside the body").
Any other destination keeps O3 FAIL. Verdicts are per binary: each
verdict line carries the body's optimization level (from optnone).
`_bfd_error_handler ROLE(pure)` is a leaf premise: it formats and prints
through the global hook, and its indirect call is checked after the
solve (pure over icall: a target with a pointer store, a block copy or
an indirect call breaks it, so a vararg pointer stored there fails it).
Case: test/t_cells_container_poolchunk.c.

## Method-installed state (TaggedFields entry tests, CellSolver formal split, 2026-10-12, plan 3.54)

A method M installed in a function-pointer field D of struct S, with a
data field F of S written alongside it (libtiff's tif_decoderow and
tif_data; the kernel's f_op and private_data; sqlite3's pModule and
pVtab). This is item 9 of the keys above, with the method pointer as the
tag and the dispatch as the test.

**The test.** A dispatch site `o->D(o, ...)` is a test of D on o. The
callee is a load of D on the receiver (dispatchReceiver, one level), and
nothing is written between that load and the call (no store, no call).
- When the dispatch enters M, D == M held at the load.
- F holds then what it held at the load.

**The read.** Inside M, a read of o'->F, where o' is M's receiver formal
(its identity, by the reaching-definition rules of item 9), gets the
entry test D == M. Its admitted writers are those whose tag set
contains M, by item 9's evaluation unchanged: retags, last writers,
alias assumptions and flips all apply.

The entry test is made only when:
- M is installed (its address stored as a constant) in D. M may be
  installed in several fields D1..Dn: the read's admitted writers are
  then the union over the Di of the writers co-written with M in Di
  (every writer if any Di admits every writer), intersected with what
  the read admits on its own. The formal is split only for dispatches
  through test sites of fields every one of its keyed reads was keyed
  through (the intersection of the reads' field sets); a dispatch
  through any other field is an other entry;
- M's address does not reach the outside (taggedOutsidePre: entries
  the solve does not see);
- no write to F of the object can come between M's entry and the read
  (item 9's stability check, from the entry block).

A retag of D (a method swapped without its state) is item 9's retag. A
write of F between the entry and the read refuses the test, and the
refusal is printed with its reason.

**D in an embedded struct (3.54 (a)).** A method field inside a struct
embedded at a constant offset (tif->tif_tagmethods.vsetfield: two GEPs at
-O0) is named by its offset in the outermost struct, as one GEP or the
-O3 struct-path TBAA tag names it; the object is the outermost struct's.
- Only through a struct whose fields are accessed inside that one
  embedding and nowhere else (no field GEP from another base, no TBAA
  access naming it as the base). A struct also used on its own keeps its
  own field names, so a field never has two names.
- The dispatch's level steps through the chain of constant GEPs
  (dispatchReceiver, the solver's receiver levels, slot offsets).
- The certificate composes too: an embedded struct's address used only
  as the base of its fields' constant GEPs is not an escape. A store
  named by the embedded struct alone covers D as well.
- An embedded struct's address used any other way is the escaping
  address of every byte of it, [o0, o0 + sizeof), by exactly the test a
  field's own address gets: a byte is certified or not whatever GEP
  spells its address. The escape check has no bodiless exemption; the
  "bodiless callees write no struct slot" premise is for path stability
  and is not widened into the certificate (zlib does write z_stream
  fields: libpng's zstream pair is uncertified, its address escapes at
  the zlib calls).

**Saved and restored methods.** A codec's cleanup restores the method
it saved at install (`tif->tif_tagmethods.vgetfield = sp->vgetparent`),
then frees its state and writes F = NULL. The restored value is not
evaluated (an unknown tag). As for any tag store, a tag its object's
content is never read under (D or F rewritten first on every path)
retags nothing. Two places now apply that rule:
- A call-site effect (the restore in a callee, TIFFPredictorCleanup)
  whose callee can execute no tested read of F, and after which the
  content is never read under the tag it leaves. "Mapped only" (every
  path meets a tag write computed from the left tag first) counts as
  never read when each of those writes is itself never read under.
- A store of a vector of pointers (-O3 restores two saved methods with one
  `<2 x ptr>` store) is a write of each lane's field with an unknown
  value: a tag store like any other, own to the certificate.

**Terms along the receiver (3.54 (b)).** The tag is a fact about the
object (which installer ran), and passing the object on does not change
it.
- An object entering method X through a test carries the term {X}.
- A call in X that passes X's receiver identity as an argument is a
  channel when the F fields read under terms are unwritten from X's
  entry to the call (item 9's stability check; its alias assumptions go
  to those fields' pairs).
- The callee's formal, when it is a split method formal, receives X's
  state for each object through that channel: X's terms, or "other" if
  the object entered X otherwise, X is not split, or X holds no state
  for it. Later changes at X follow (monotone).
- Inside callee Y, a keyed read of o->F for an object carrying term
  {X} also admits the writers whose tag set for each D of X's tests
  contains X; every writer when the read is not keyed under one of those
  D. The dispatch test is the case X = Y.
- A static edge into the formal is a channel only if every call
  argument with that node is one, from one caller formal; else it is an
  other entry.
- A channel is a transfer the argument's pops make, not a copy edge, so
  saved-parent chains (every VSetField's parent may be every VSetField)
  close no copy cycle for the collapse to merge. The term lives on the
  entry edge: the cycle collapse, lossless for facts, is lossy for
  terms, so the formals must not merge. A method passing its
  receiver into its own formal adds nothing: by the identity check the
  argument is the formal's own value, already there.

**The split.** The entry test holds only for entries through a test
dispatch, so the solver splits M's receiver formal A:
- Every other entry arrives at a node Ao, which feeds A: every static
  edge into A (direct calls, call sites wired by resolution, seeds) and
  every dispatch through a site that is not a test of D.
- An object that ever arrives at Ao, or that a fact at Ao comes to
  stand for after a cell merge, is "other". Each entry-keyed read also
  reads it unkeyed, through the read's entry hub.
- An object that has entered A only through test dispatches is read
  through the admitted keys alone.
- If A, Ao or a channel into A is merged with another node (a cycle
  collapse), or A's node is shared, the formal is not split: every
  object reads unkeyed, and so does every object it passed on.

All of this is monotone. An object becomes other and gains the unkeyed
link at any point of the solve, and nothing is unlinked.

**Soundness**, per entry:
- Through a test dispatch: item 9's argument with the test at the
  dispatch's load. The content F holds at the read is a writer's whose
  tag set contains M.
- Through a channel from X: at X's entry the content F held was a
  writer's whose tag set contains a term of the object (by induction
  over the channel chain, the base case a test entry); F is unwritten
  from X's entry to the call and from Y's entry to the read, so the
  same content is read.
- Through any other entry: the unkeyed read, every writer.

The rows are in the rule report: "T entry" per method formal (D, the
installers, the reads keyed, the test sites), the refusals by reason,
and per formal its test-dispatch and other entries and the objects read
unkeyed.

Cases: test/t_tagged_method.c (each codec's method sees its own state)
and test/t_tagged_method_direct.c (a direct call sees both). Probes,
recorded in the commit: a method swapped without its state; F written
in the method or by a callee before the read; a method installed in two
fields; a method's address passed to a bodiless function.

Not mechanized. Checked by executions; see the 3.54 commit's gates.

## Objects are named by their allocation sites (CellSolver seeding, 2026-10-14)

The global dedup merges copy-equivalent value nodes before the graph is
built (casts, zero-offset GEPs, all-same phis, a single-callsite actual
with its formal), and union by rank picks each class's representative.
An allocation's class can be represented by a formal or a cast: the
kernel's acpi_pci_root_add allocation shares a class with
acpi_pci_root_create's formal. Graph build records the site under its
class representative (AllocSites), and the cells solver seeded the
object from the representative's value. The object was then named and
labeled by that value: the azx bus object was labeled struct.hdac_bus
(its embedded struct) by its first typed use, not by its allocation.

- **Statement:** an object's Value is its allocation site. Graph build
  records each site's own value node beside the representative, and the
  solver seeds one object per site, with the site's own node as origin.
  Two sites in one class are two objects, both in the class's facts.
- **Asserted:** every allocation class has a site, and every allocation
  node seeded has its own node. The log counts the sites seeded under a
  representative that is not the site, by the representative's kind, and
  the classes with more than one site.
- **Facts:** the class's facts are unchanged (the class still holds the
  object). What changes is the object's name, its label and its extent,
  which are read from the site.
- **One pointer, one carve:** a pool carve is recorded at its value with
  casts and zero-offset GEPs stripped. A before-bump carve's phi and the
  phi's bitcast were two carves of one pointer (bfd_hash_insert,
  _bfd_stringtab_add); they shared one class, so they were one object
  only by the dedup. Recorded once, they are one site.

Case: test/t_cells_allocsite.c (malloc under a formal's class, at -O1).
Not mechanized. Checked by executions; see the commit's gates.

## Link words (LinkWords.cc, report only, 2026-10-15, plan 3.55 R1 step 1)

An integer field that holds a pointer whose low bits carry data
(rb_node.__rb_parent_color = parent | color) is classified, before any
solve, by the shapes of its stores and loads. The flow is not changed:
the integer round trip (ptrtoint | k, masks, compares, inttoptr) already
keeps p's facts (ptrToIntTagRoundTripOnly); this adds the checked name.

- **Statement:** a candidate (a pointer-width integer field with a load
  reaching inttoptr) passes when every store's value is a tagged word
  (ptrtoint(p), a constant < 8, a copy of a passing field, or/xor with a
  tag value, add of a tag value onto a word with known-zero low bits, a
  clear `& c` with ~c < 8, phi/select of these) and every load's uses end
  in inttoptr, a compare, a tag extraction, or a store into a passing
  field. A greatest fixpoint over candidates (a copy's status is its
  source's).
- **Assumed, per site:** an inttoptr with no clear on the way (rb_red_parent)
  relies on tag 0 at that read: an ASSUMPTION line, not checked.
- **Naming with no struct GEP at leading index 0 and no TBAA** (the
  kernel builds with -fno-strict-aliasing and the 5.18 corpus has no
  debug info): a GEP's source struct names its base only at leading
  index 0; any other constant GEP (a non-zero leading index, which
  InstCombine makes of `&hc->uuid_node` as `(rb_node *)hc + 1`, or a byte
  GEP) contributes only its byte offset to its base's name, and that
  offset must stay inside the base's struct, else the access is "a step
  past the layout of S" (unnamed, counted apart: the base's enclosing
  struct is unknown). A pointer is named by its declared pointee, by
  debug info; else by the object's own IR type (1b: a global's or
  local's value type when it is a named struct, or an array of one; a
  struct GEP of another struct on the same object, both normalized to
  their innermost struct at offset 0, is a pun); else by sibling GEPs
  (the value is the base of leading-index-0 struct GEPs of one struct in
  its function, after the same normalization; two structs are a pun:
  unnamed; the name is the widest of them, so a byte step keeps its
  extent); else by formal provenance (a function whose address is never
  taken: every call site's actual names the same struct, after the same
  normalization). A use from a ".discard*" section (EXPORT_SYMBOL's
  __addressable marker) does not take the address: the linker drops it.
  An access none of these name is counted per function; a copy through it
  fails its field "on naming". Before 2026-10-15 a non-zero leading index
  was read as the GEP's source struct plus an offset outside it, which no
  field holds: the access was silently unnamed in R1 and silently matched
  no slot in the container check.
  The same route for every client of accessSlot (Fable 2026-10-16; the
  tagged fields, the census, carves, the int-name flags, the summaries'
  slot keys): a struct GEP at a non-zero leading index is a byte step,
  named only by its TBAA tag, else unnamed and counted. Before, accessSlot
  named it by the step's own struct and the offset past it: nm-O3's
  TaggedFields keyed the tag "struct.bfd_link_hash_entry+96" (56 bytes),
  which is elf_link_hash_entry's field written as a step over its first
  member's type. An unnamed step's address taken is no escape of a named
  field: stores through it are classified by their pointer's provenance.
- **Anonymous structs name nothing** (Fable 2026-10-16): clang numbers
  them (`struct.anon`, `struct.anon.12`) and the linker's suffix strip
  makes every one `struct.anon`, so a field inside one was a key shared by
  every anonymous struct in the program (binutils' bfd_link_hash_entry
  u.i.link and an unrelated `struct.anon+8`: one cursor key). A field of
  an anonymous struct is named by the nearest enclosing named struct on its
  access's GEP chain (each step at leading index 0) and the byte offset
  there, as struct-path TBAA names it at -O3 (bfd_link_hash_entry+40 at
  both levels); with no enclosing named struct on the chain (a pointer to
  the anonymous struct itself), the access is unnamed, counted ("anonymous
  struct fields: n named by the enclosing named struct and byte offset, m
  unnamed"), never the shared name. The innermost-field key stops at an
  anonymous struct the same way, and debug info's pointer members include
  an anonymous member's members at its offset (the links a block infers).
  The same rule everywhere a struct's name is read, through one predicate
  (GraphBuild.cc isAnonStruct beside stripStructNameSuffix, whose ".N"
  strip stays right for a named type's link rename): access names
  (NamedCells isNamed) treat an anonymous struct as transparent, the
  enclosing named struct's offset accumulating, and an access with no
  named struct around one is no-struct (counted); accessSlot (tag tables,
  TaggedFields, the census) names it by the enclosing named struct on the
  chain, else by its TBAA tag, else not at all; the cell solver labels no
  object by an anonymous type (a global or stack object of one, or a typed
  write that would label one, stays unlabeled: cells by byte offset, size
  kept), and a step of an anonymous type fits a layout only as that IR
  type itself (structStartsAt, sameType, sameStruct); UnionCensus
  positions an address whose chain starts at an anonymous struct by its
  base pointer's declared struct and offset, else not at all (counted).
  The linked IR can give a named C struct an anonymous IR type (the IR
  linker merges isomorphic types: nm's elf_internal_dyn is
  `%struct.anon.20`); debug info then names its fields by the C tag
  (struct.elf_internal_dyn+8). Never a per-module name: clang numbers one
  anonymous type differently in two modules, and a name that differs
  between modules would separate a store from its load. The IR linker
  renames a colliding anonymous type again (`struct.anon.9.932`), so every
  numeric suffix is stripped before the name is judged. The one residual
  ambiguity: a C struct literally tagged `anon` (`struct anon { ... }`)
  has clang's anonymous name and is treated as anonymous; it is not
  special-cased (the treatment only withholds names, so it is sound).
- **Unions stop the name** (Fable 2026-10-15, class 2): the IR's type of a
  union is clang's representative member, never the program's choice
  (5.18's timerfd_ctx `union { struct hrtimer tmr; struct alarm alarm; }`
  is `{ %struct.alarm }`, so tmr._softexpires at +32 reads as
  alarm.timer.node.node.__rb_parent_color). A layout path that crosses a
  union names the enclosing struct and the byte offset there; the access
  is "storage inside a union", counted, not an access of the
  representative's field. A link word copied into or out of such storage
  is an ASSUMPTION line of the field (union keys, plan 3.17, decide it
  later), not a naming failure. Without debug info the IR has no other
  member to consult.
- **Scope:** the classification reads SSA. At -O0 a value passes through
  a local slot, so -O0 code is out of scope by design (like the -O3
  typing); its fields fail as copies from unnamed accesses.
- **Pointer fields** that receive encoded words (XArray slots: node | 2,
  values, internal constants) are reported by shape only (R1 addendum (b)
  is measured, not built).
- **Worked example: an ASSUMPTION site's consequence** (kernel why runs on
  72c3496, 2026-10-15). RB_CLEAR_NODE in timerqueue_del stores the hda
  codec's suspend-timer node address into its own __rb_parent_color
  (hda_codec+296; R2's self-link, which stays in the element's cells).
  rb_insert_color reads that word as the node's parent and converts it
  unmasked (`%98 = inttoptr` of the loaded word: an ASSUMPTION site, tag
  0), then stores the "parent" into the node's own rb_right (hda_codec+304).
  rb_next's rb_right load returns the node, and rb_next's return, shared by
  every tree, carries it to proc_keys_start, which steps it as struct key.
  Every read and write targets the right cell for the value it carries:
  the loss is the sentinel read as a parent (flow-insensitively: the
  program overwrites the word in rb_link_node before any insert) and the
  shared traverse return (cured by traverse rows by derivation, R5).

Cases: test/t_cells_linkword_{rb,rotate,plus8,addtag,xarray,sibling,union}.c.
Not mechanized. Checked by executions; see the commit's gates.

## Containers in report mode (Containers.cc, ContainerOwnerCode.cc, 2026-10-15, plan 3.55 R3/R5)

A `@container NAME report` block in func_summaries.txt (the kernel's
rbtree and llist, rows as ruled in R5) is checked like any container and
reported per container in the log and the rule report; its rows are
never applied.

- **Statement (no fact changes):** a report block adds no edge, no row
  link and no mint; the solver's facts and answers are those of the same
  run without the block. Checked by executions: the cells and consumer
  gates on programs without the rows' functions are byte-identical, and
  t_cells_container_report keeps both targets of a lookup a row would
  narrow.
- **Declared storage** (`@storage HANDLE(T+off) LINK(T+off)
  LINKWORD(T+off)`): a proposal named by the innermost struct holding
  the slot (rb_root+0 matches the rb_root inside any owner), checked from
  both sides: (i) every element-derived store in a row body or in owner
  code lands in a declared slot (an address that may name an undeclared
  field fails "an element stored outside the declared storage"); (ii)
  every write into a declared slot anywhere in the program is a row
  body's or an admitted site, else O1 fails with the site. A declared
  slot nothing writes is counted "unused declared storage", not a
  failure. Where the program has debug info, the declaration must agree
  with it (links: pointer members back into the container's structs;
  handles: pointer members). A LINKWORD needs its R1 verdict PASS (or
  PASS with assumptions, carried into the container's lines).
- **Admitted writes (premises, counted):** null stores and fills, a link
  word's null plus tag (R1); a self-link (R2: the element's own object
  address, tagged or not, into its own slot: it introduces no other
  owner's element); a link word reused as an integer (R4: a constant, or
  arithmetic over a load of the same cell); a same-cell re-store (an
  atomic's tied old value, R4 family); a same-owner re-store in owner
  code; an implicit insert; a link store on the element an insert row
  call in the same function takes.
- **Owner-code derivation (D5):** in a function that passes owner value
  o to a row, a value or slot is derived from o when it is o's
  handle-slot address or load, a link (or decoded link word) address or
  load of a derived value, a phi or select all of whose non-null entries
  are derived (a greatest fixpoint: loop-carried descents close), or a
  row's result on a derived argument; an element argument of a remove row
  on o is derived. An owner or element whose own address names a declared
  slot (a handle or link at +0) is that slot's address. A phi or select of
  field addresses names every entry's field.
- **Implicit insert (D6):** a store of a pointer into a derived slot is an
  implicit insert site, matched when an insert row call in the same
  function takes the same element (SSA value) and the same owner value
  (SSA value or constant GEP shape); an unmatched one fails O1 with its
  site. A row that is also owner code (timerqueue_add calls
  rb_insert_color) is checked both ways. A store whose address is a
  derived slot of several owners in the function is judged by all of
  them, never by the first one visited (Fable 2026-10-21): it is a relink
  if it is one under some owner; otherwise an implicit insert, matched
  when some owner it is a derived slot of has the pairing insert row call
  (that call's owner is the slot's owner); otherwise a link store on the
  inserted element if it is one under some owner. The subset's
  xfrm_policy_inexact_insert_node stores node %269 into the root or a link
  of the inner tree %130 = &n->root, n an element of the outer tree %1:
  the slot is %130's, matched by rb_insert_color(%269, %130); under %1 it
  is only an element's field.
- **Inline asm (D4):** an asm's memory effects are the graph build's
  model (asmModel, called by both): an indirect output stores each direct
  pointer (or witnessed pointer-width) input, an indirect input is read
  into the result, raw pointer inputs are read and, with memory effects,
  written with every value input. The checker judges those stores and
  loads like any other.
- **Naming:** one rule with the link words (struct GEP, TBAA, an array
  member at a variable index, else the resolver at offset 0). An access
  through an owner or element value that no rule names is a naming
  failure ("FAIL on naming", sites listed), never a pass. A pointer
  loaded from a field has no named pointee without debug info (rule (2),
  field pointee inference, not built): the kernel's llist bodies fail on
  naming, which the report measures.
- **Row premise (1c):** a row types its OWNER formal as the struct of the
  block's HANDLE at +0 and each ELEM formal as the struct of its LINK and
  LINKWORD slots, in the body and nothing else (every other value is still
  named by derivation or a naming route). The premise is discharged at
  every call site: an actual named by a route as a struct that holds the
  premise's struct at that offset (classes 1-3 below) agrees; an
  actual named as another struct fails the row at that site; an actual
  nothing names is a per-site ASSUMPTION, listed (the same shape as R1's
  unmasked inttoptr); a null actual carries no object.
- **Asm model over-approximation:** the model's raw-pointer rule writes
  every value input through every raw pointer input (llist's cmpxchg
  writes new_first and the old head through each other). Such writes fail
  under their own class. A constraint-aware model (only memory-constrained
  operands are addresses) would remove them, and is unsound without
  reading the asm text where a register pointer is dereferenced: a
  measured follow-up.
- **Traverse rows:** RET is the element set of the containers that contain
  the ELEM argument (its O3 containment set); an element no container
  contains leaves the call to the body ("traverse of an uncontained
  element"). Specified for enabling; nothing is applied in report mode.

### Report-arm rulings (Fable 2026-10-15, after the whole-kernel report at a297146)

The whole-kernel FAIL mass was mostly the checker's own naming gaps. Each
class below is counted and listed in report mode; applied mode inherits
the listed ASSUMPTIONs.

- **Class 1, embedding through arrays:** a premise actual inside another
  struct agrees when the struct analyzer's embedding table (transitive,
  every array element: latch_tree_root's `rb_root tree[2]`) holds the
  premise's struct at that offset, looked up by the actual's own struct
  type (anonymous structs share a name across modules). The table is
  cross-checked against the IR layout walk; a disagreement is printed.
- **Class 2, unions:** a layout path crossing a union stops (see Link
  words). Premise: with debug info, the actual agrees "through the
  union" when a DI member of the union at that offset is or embeds the
  premise's struct, and fails otherwise; without debug info (the 5.18
  corpus) the site is an ASSUMPTION "inside the union at S+o (members not
  in the IR)", provided the premise's struct fits in the union from that
  offset (else FAIL). Storage: a write whose bytes reach a declared slot
  only through a union's representative member is "storage inside a
  union", counted, not a write of the slot. Rebuilding the corpus with -g
  turns this class into checked agreements or failures.
- **Class 3, a step past a named base's layout:** an ASSUMPTION in the
  premise, unnamed in R1 and in storage ("a step past the layout of S",
  split out of the naming failures). Only a base nobody names wider
  stays in the class: the 5.18 kernel's container_of steps (EXT4_I's
  inode-296, alarm's hrtimer-32, work_struct offsets) and InstCombine's
  `(rb_node *)hc + k` when clang rewrote every access of the object as an
  rb_node GEP.
- **Inlined removes (the link invariant):** rb_erase_augmented and
  rb_erase_cached inline into owner code; the removed node reaches no row,
  only its rebalance parent (`__rb_erase_color(parent, root, rotate)`)
  does. In owner code a node whose link read (a LINK field, or the
  LINKWORD decoded) is an element by D5 is an element too, a greatest
  fixpoint with D5, each node listed "inlined remove: node assumed an
  element by its parent word"; its stores are then owner-code relinks.
  This is the premise the remove row's ELEM already carries: a program
  that erases a stale node whose links still point into the container
  violates it exactly as it would violate rb_erase's ELEM premise. Both
  are the container's well-formedness, not a flow fact derived here.
  Owners and elements are identified by object and offset (a step from
  the object to a declared slot whose struct starts at an owner's or
  element's offset is that one's slot: `&mm->holes_size.rb_leftmost`).
- **Owner-code relinks (4(a)):** a store of a derived value into a derived
  slot (an inlined remove, a rotate, __rb_change_child) is admitted and
  counted; only a store of a value not derived from the owner is an
  implicit insert that needs pairing.
- **Pairing (4(b), D6 refined):** owner identity is the object plus the
  constant offset (rb_root_cached and its rb_root at +0 are one owner;
  rb_leftmost at +8 is a HANDLE of it); the same element is the insert
  call's actual, a value it merges through phis and selects
  (rb_insert_augmented_cached's `*link = node` on the empty-tree path), or
  the same object and offset.
- **Traverse elements in owner code:** in a function with exactly one owner
  group, a traverse row's ELEM actual (`rb_next(node)` in an inlined
  rb_erase_cached) joins that group: a per-site ASSUMPTION, listed. In a
  row body, a traverse row's result on a derived element is derived (D7).
- **Rows:** `__rb_erase_color` takes its parent as ELEM(arg0) (an element
  already in the tree); rb_replace_node(_rcu) take the victim as a second
  ELEM: `*new = *victim` copies the victim's link record, its parent word
  and color included (the new node inherits the victim's parent word,
  which is the operation's meaning), admitted as "a copy of an element's
  links (with the link word's tag)"; O3 follows the new node through
  ptrtoint and R1's tag ops into a declared LINKWORD store as a link
  store.
- **Inline insert with no row symbol:** an element stored into a handle in
  a function that calls no row (rethook_hook's `__llist_add`, static
  inline) is an honest FAIL in its own class, counted and listed; a
  body-shape match is deliverable 2.

### Residue of report arm #2 (Fable 2026-10-16, after the whole-kernel report at fc2f459)

- **An element pointer kept in a plain field (D2(i) refined):** O1
  constrains stores into declared slots and stores of link values, not
  every copy of an element pointer. An element stored into a field of a
  struct the block declares no slots of (ext4_readdir's `info->curr_node`,
  a cursor) is ordinary flow the solver carries: counted, listed, never a
  FAIL. Soundness of the rows does not rest on this check: it is carried by
  O2, since a lookup's or traverse's RET derived from an undeclared field
  fails provenance. An element stored into a pointer field of a struct the
  block declares slots of that holds no declared slot (a fourth pointer in
  rb_node) stays the D2 FAIL "an element stored outside the declared
  storage": evidence that the storage proposal is incomplete, the proposal
  checked from the program's side. A union's members are class 2, not this
  test.
- **Identity by object and offset, everywhere (4(b) completed):**
  - an owner or element value is recognized by its object and constant
    offset wherever it appears, not only by SSA value (S1: the group keeps
    `&epi->rbn` stripped to `epi` when the element is at +0, rb_next's
    actual is the unstripped zero-index GEP);
  - a phi or select whose entries agree on object and offset is that object
    and offset (S3: rb_add_cached computes `&root->rb_root` and
    `&node->rb` on both paths and passes the phis to the row);
  - by byte arithmetic from a derived value, the intermediate GEP types
    irrelevant (S4): a pointer at the value's own address is the value; one
    at a declared slot offset of the element struct is that slot; a GEP
    whose only variable index is a select or phi of constants is the set of
    its constant steps, each of which must be a slot (interval_tree_generic's
    `rb_entry(parent)` then `&parent->rb_left / rb_right` as a word index,
    find_va_links' `&va->rb_node` rebuilt from the node).
  - Constant addresses that name an owner's or element's slot are known
    before the derivation (S2: a descent from mod_tree's root read through
    a constant GEP is derived).
  These add no premise: the identities are the program's own arithmetic.
  Values derived through them make the container_of reads from those
  values visible as naming failures ("a step past the layout of rb_node"),
  which they were all along. The classes a value has by its object and
  offset are part of the derivation's result, for every reader of it (the
  O1 check reads `&root->rb_node`, a zero step, as its object).
- **Slots at a union actual (S5):** an owner or element actual whose
  premise is "inside a union" (an ASSUMPTION without debug info; "through a
  union member by debug info" with it) has its declared slots at actual +
  k as slots, under that same assumption, listed once per actual
  (vma_interval_tree_remove's `&vma->shared.rb`, kernfs's children root,
  sk_buff's rbnode). No new premise: the row call already assumes the
  struct is there.
- **The owner read twice (S6):** two loads of one named slot (one field
  key at one address shape), the first dominating the second, are one
  value when every write on a path between them that runs neither again is
  named and none has the slot's name; a row call's write set is its
  declared storage: checked, counted. An unnamed write or a call to a
  function that is not a row between them makes the identity a per-site
  ASSUMPTION "owner re-read from the same slot". A write of the slot's own
  name keeps them apart. Used by the owner groups, the owner-code
  derivation (object identity) and the owner shapes (D6 pairing, (d)).
  Across branches (Fable 2026-10-16): with no dominating read, the second
  read is one value with a virtual read at the nearest common dominator of
  the two, the same write test on every path from it to each read (nm-O0's
  `info->hash` reloaded on both arms at linker.c:1785); reported as "across
  branches", each site listed.
- **Descents from a node not derived from the owner (S7), never a FAIL:**
  - a formal of the function at its own address, merged into a descent (a
    phi or select whose other entries are derived), is a listed ASSUMPTION
    "descent from a node assumed an element" (insert_vmap_area_augment's
    `from`);
  - a pointer field of an owner's object that is not declared storage,
    into which owner code stores an element of that owner (derived, a row's
    result, or an inserted element, through its object at offset e): when
    every store into the field program-wide (by name) stores null or such an
    element of the owner whose object holds the field, at one offset e, the
    field is a CLOSED CURSOR and its reads from an owner's object are
    derived elements at +e (inet_frag_queue's fragments_tail); otherwise
    each read is a per-site ASSUMPTION "a node read back from a plain
    field". A field whose stores carry elements at several offsets derives
    nothing (no one element a read could be).
  - a descent that starts at a formal OBJECT's node at +e, e the element
    actuals' offset in their objects (not 0, not an actual's own object;
    a LINK slot of it read and the node used as a node, or the node merged
    by a phi or select), is the same premise in another dress: a per-site
    ASSUMPTION "descent from a formal object's node at +e" (Fable
    2026-10-16 Q1: vma_interval_tree_insert_after's `prev` at +88, inside
    the union as the actual's, then also a union actual's slots;
    drm_mm_interval_tree_add_node's hole node). A constant step k over a
    phi or select of objects each of which has an element at k is an
    element (the phi meet over objects: insert_after's parent word
    `&parent->shared.rb`, parent a phi of container_of(node) and `prev`).
- **An asm by its model (D4, Q2):** an operand both read and written (an
  output memory operand with its input, `+m` or `=*m` with `*m`) is a load
  of the slot into the asm's result and a store of its inputs. Through a
  derived HANDLE the result is an element: an inline llist_del_all is
  `xchg(&head->first, NULL)`, a remove-all lookup by the asm model
  (i915_active's barrier tasks: the detached chain rebuilt by
  `node->next = previous` are relinks, llist_add_batch re-adds it on the
  same head). An owner value at its own address is its declared handle at
  +0 by the row's premise, named or not.
- **One report text:** every listing in the container report is sorted,
  so one input gives one text whatever the binary's heap layout (groups
  and bodies are keyed by pointer).
- **An owner read through a pointer (Q-b, Fable 2026-10-16):** a lookup
  row's OWNER(*argN@off) names the table at byte off of the formal's
  pointee (bfd_wrapped_link_hash_lookup: bfd_link_info.hash at +40). Debug
  info checks it (the pointee's member at off points to an owner type;
  else the row FAILs and the block does not hold). It is applied through
  its body: the function is no row link and stays out of the application
  body set; its body is classified and checked (O2) like the body's, and
  its callers' elements are its inner lookup's. A call's owner is the slot
  *(A + off), one value with a real read of that slot in the caller (S6),
  else a value of its own. Deferred: a RowLink owner-deref form for the
  solver (never an unverified load of the slot at the call).
- **Closed cursor fields on elements (Q-a, Q-e):** a pointer field of an
  element into which every store program-wide (by name, block copies by
  cover) is null or an element (in the body by class, outside by
  elemOwner) is a CLOSED cursor. The cursor verdicts are those of the
  greatest fixpoint in which every field a verdict leaned on ends closed:
  a field under way reads as closed, a verdict that read another field so
  leans on it, and a field that ends open withdraws every verdict that
  leaned on it (transitively), decided again on its next use; premises
  are listed only for fields that end closed. A read of
  it from an element is an element of the same owner, under the listed
  per-field premise "the element stored there is of the same table
  instance". An ELEM(ret) row's RET may be a payload read only through
  closed cursor fields, each payload read on its derivation included (a
  load through a payload value is payload again: `ret = ret->u.i.link`);
  a body read of a closed cursor field discharges O6 under the same
  premise.
- **One greatest fixpoint, values too (F1, Fable 2026-10-17):** all the
  container verdicts are one greatest fixpoint. Whatever is under way, a
  cursor field, a value's element evaluation (an -O0 slot's or a phi's
  entries), or a read of a cursor whose other members' keys are not known
  yet, is assumed (closed, an element, admitted) inside the evaluations it
  encloses; every verdict that rested on it is withdrawn when it ends
  otherwise, and decided again on its next use. A cursor field whose check
  began inside a value's evaluation and met that value as a stored element
  leans on it, and is withdrawn if the value ends no element; a read
  passed while its cursor was under way is checked once the cursor's keys
  are known, and a refuted read fails from then on, its cursor deciding
  again (each round refutes one more read: it ends). The inconsistency
  this removes: a value under way was treated pessimistically (not an
  element) while a cursor under way was treated optimistically (closed).
  On nm-O0 the cursor bfd_link_hash_entry+40 was first checked inside the
  evaluation of the source h of linker.c:1785's copy (`h = h->u.i.link`
  is one of h's stores), met h under way as the copy's source, and came
  out open on it, which then failed h. With withdrawal the verdicts do not
  depend on the order the checks reach them; no pre-pass is needed.
- **Named holders (rule A, Fable 2026-10-17):** memory that is no field of
  an element but holds entries is a holder when every store into it can be
  enumerated by name (never by flow facts, which would be circular): (2) a
  local whose address goes only to loads, stores, comparisons and actuals
  of direct calls, followed into each callee formal that receives it (the
  formal's -O0 spill reloads included), transitively; (3) the pointee array
  of a named pointer field (elf_obj_tdata's sym_hashes): the stores through
  pointers derived by name from reads of the field (index steps, -O0 locals
  whose every store derives from it, a local under derivation agreeing:
  `p = p + 1`), pointers into it passed to a callee followed into its
  formal; (3') the pointee array of a local pointer whose every store is a
  fresh block or null (binutils' sorted_sym_hash = bfd_malloc (..)), its
  stores derived by name from that local in its own function and followed
  into callees. A local holding a fresh block and another pointer is no
  holder (counted). (1) is the cursor field above. A holder read is
  evaluated in the same greatest fixpoint (the holder is a value under way
  while its stores are evaluated): closed (every store null or an element)
  it is an element under the premise that the element stored there is of
  the same table instance, listed per holder; OPEN-REFUTED (a store of a
  value known to be no element: a global object, a function, an integer)
  it is no element; OPEN-UNPROVEN (a store of a value of unknown status, a
  use no rule follows: an address stored to memory, a bodiless or indirect
  call, a block write the engine cannot attribute) it is admitted as an
  element under a per-site ASSUMPTION naming what keeps the holder open,
  counted in "VERIFIED under n". Owners are named per function, so a
  holder's stores in several functions are not compared: a holder read is
  an element of no one owner shape, and O1's same-owner pairing, which
  needs one owner, does not take it (a copy from a holder read stays
  "another value").
- **A copy of the whole struct (Q1 (b), Fable 2026-10-17):** a block copy
  between two objects of one struct (the destination's and the source's
  named slots the same struct at offset 0, the length its size) is
  key-preserving: under each key the destination's content is the
  source's, tag and union bytes moving together (3.53 rule 4, cell to
  cell). Under a cursor's keys it moves the cursor's own content, so it is
  no store into the cursor, with no owner condition. This is what a block
  copy's elementStored(source) means in general: under each key the copy
  stores the source's content under that key. O1's admittance of the link
  words a copy covers keeps the same-owner condition (the rb_replace_node
  rule).
- **A cursor inside a union (Q-d):** a store of another member over the
  cursor's bytes is no store of the cursor only by the union keys (3.17 /
  3.51, the keys an access carries), never by a discriminator read here:
  every such store keyed, every read of the cursor keyed to admit none of
  their keys. A read admitted by the union census's own-member key with no
  settling check (an UNCHECKED read, the user's 2026-10-07 rule) makes the
  closure rest on that assumption: listed per read and counted in "VERIFIED
  under n assumptions"; a read a tag pair keys is checked and adds nothing.
  Without keys the field is not closed: "cursor inside union u
  (S+off): no admitted discriminator", with the union census's and the
  tagged fields' words (nm: bfd_link_hash_entry.u, whose members are
  structs the census does not type by member, and whose tag `type:8` 3.51
  widens at elflink.c:5250's bitfield write). The containers are checked
  after the union keys and tagged fields for this (under --cfl-cells no
  step between the check's old place and its new one runs).
- **The caller's out-parameter (Q-c):** a load of a formal's pointee at +0
  (`*hashp`) agrees with the other entries of a slot or phi as a per-site
  ASSUMPTION "element from a caller's out-parameter, assumed an element of
  the owner"; alone it names no owner. Slot and phi entries must agree
  (S3 for stores). A block copy between two elements of one owner is
  admitted (rb_replace_node's link-record copy, generalized).
- **Verdict text:** a block that holds only under listed assumptions is
  "VERIFIED under n assumptions", never a bare VERIFIED.

Cases: test/t_cells_container_{rb,rb_unmatched,storage_bad,llist,llist_int,report,naming,
embed_array,union,union_nodi,past_layout,cached,inlined_remove,replace,inline_add,cursor}.c,
t_cells_container_{zero_gep,const_root,phi_owner,bytestep,union_slot,reread,descent,formal_obj}.ll
(shapes from the kernel's clang-14 IR that clang-18 no longer emits) and
t_cells_container_del_all.c, t_cells_container_{cursor_closed,cursor_open,cursor_union,
cursor_nested,deref_owner,outparam,cursor_union_copy,cursor_underway,holder_outparam,holder_outparam_refuted,
holder_outparam_escape,holder_array,holder_local,holder_local_other}.c (the bfd link-hash rows); rows for the rbtree cases in t2_cells_rblib.c,
shapes in cells_rb.h.
Not mechanized. Checked by executions; see the commit's gates.
