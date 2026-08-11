# Soundness proof (paper draft, 2026-08-08)

Slots into §3.2 (statement + proof-architecture figure in the body,
full rules and theorems in an appendix). Every theorem below marked
[Lean] is machine-checked in `proof/lean/CompositionalCFL/FlowsTo.lean`
(no `sorry`, no axioms beyond Lean's kernel); the Lean name is given
so reviewers can audit. Assumptions are named A1–A3 and each one
states its *enforcement mechanism* — this proof's discipline is that
nothing is assumed silently.

---

## The claim

> **Theorem (answer soundness).** Let a program run reach an indirect
> call site *i* and invoke function *f*. Then (*i*, *f*) is in the
> reported answer set, provided A1 (encoding adequacy), A2 (boundary
> closure), and A3 (certified fixpoint).

The proof is a stack of four layers. Each layer's conclusion is the
next layer's hypothesis, and each layer is discharged by a different
instrument — pen-and-paper audit, machine-checked theorem, or per-run
certificate:

```
runtime flow  ──A1/A2──▶  derivable in the reference grammar (Def. 2)
              ──Thm 1──▶  present in ANY closed solver state   [Lean]
              ──A3    ──▶  present in THIS run's final state    [certificate]
              ──Thm 3──▶  unchanged by staging/batching/spill   [Lean]
              ──extract─▶  in the reported answer set           [deterministic]
```

The unusual move is the third arrow: Theorem 1 is proved once, for
*every* solver state satisfying a small closure interface, and each
production run then *checks that its own final state satisfies the
interface*. The gap between the Lean model and 16k lines of C++ is
crossed per run, not per proof.

## 1. Definitions

**Definition 1 (flow graph).** The analysis operates on a directed
graph G over nodes N (equivalence classes of IR values and memory
cells) with edge labels:

- `a` — assignment/copy (shift-preserving),
- `f(r)` — field step adding byte offset r,
- `fx` — field step of statically unknown offset,
- `d` — dereference: a pointer node to its pointed-to cell.

A distinguished set O ⊆ N of **origins** (functions, globals,
allocation sites) carries the identities answers are made of. Shifts
live in Option S for a commutative monoid S — an exact offset
`some r`, or the absorbing unknown ⊤ (`none`); composition adds exact
shifts and ⊤ absorbs. The production Z_P residue bucketing is a
monoid quotient of the ground-truth instance (S = byte offsets), so
everything below holds for it verbatim. [Lean: `ShiftMonoid`,
`Shift`, `shiftComp`, `FLabel`, `FGraph`]

**Definition 2 (reference semantics).** The declarative judgment has
two forms — `flow(z, c, x)`: a value originating at z reaches x with
net shift c; and `mal(cx, cy)`: memory cells cx, cy may alias. FDeriv
is the least relation closed under:

```
  z ∈ O
 ─────────────── (R-Refl)          origins flow to themselves at shift 0
 flow(z, 0, z)

 flow(z,c,x)   x ─a→ y             flow(z,c,x)   x ─f(r)→ y
 ────────────────────── (R-Asgn)   ─────────────────────────── (R-Fld)
      flow(z,c,y)                     flow(z, c⊕r, y)

 flow(z,c,x)   x ─fx→ y            flow(z,c,x)   mal(x,y)
 ────────────────────── (R-Wild)   ────────────────────── (R-Mem)
      flow(z,⊤,y)                       flow(z,c,y)

 p ─d→ cx   q ─d→ cy   flow(z,c,p)   flow(z,c,q)
 ──────────────────────────────────────────────── (R-Join)
                  mal(cx, cy)
```

plus the two wildcard variants of R-Join where either premise holds
at shift ⊤ (R-JoinXL, R-JoinXR). R-Join is where aliasing is *born*:
two pointers carrying the same origin at the same shift (or one at ⊤)
make their cells interchangeable. [Lean: `FDeriv`; the rooting at
origins rather than reflexivity-everywhere is deliberate — see §5.]

**Definition 3 (answers).** For an indirect call through pointer node
p: Answers(G) = { (p, fn) | fn a function origin, and flow(fn, 0, p)
or flow(fn, ⊤, p) is derivable }. Resolution accepts exactly these
two shifts.

## 2. Assumptions and their enforcement

**A1 (encoding adequacy).** If a runtime execution makes the value of
function f reach the pointer of site i, then flow(f, c, p_i) is
FDeriv-derivable for some accepted c. Equivalently: the IR→graph
encoding over-approximates concrete data flow. This is the only
pen-and-paper layer, and it is *audited rather than trusted*: the
instruction-disposition check aborts on any IR construct without an
assigned encoding (nothing defaults), and §2.2's census enumerates
the channels that leave IR semantics (assembly, integer-carried
pointers, section arrays, patching families), each either modeled
with a stated witness or declined into a named ledger counter.

**A2 (boundary closure).** Code outside the analyzed corpus does not
manufacture flows into resolution except through modeled channels.
Enforced by the extern/asm boundary census re-run per corpus (the
kernel's boundary is closed — commit 5cb3585) and by the
UniversalPtr/IntProvenance ledgers, whose counters are reported with
every run: a reader auditing the theorem can enumerate exactly what
was declined.

**A3 (certified fixpoint).** The solve terminates and its final state
is closed under the solver's rules. Not assumed: *checked per run*
(§4).

Everything below Definitions 1–2 is unconditional mathematics.

## 3. The machine-checked layer

**Theorem 1 (abstract-solver completeness).** [Lean:
`solver_complete`, `answers_complete`] Define a *closed solver state*
as any pair (minted, SF) — a root predicate and a fact relation
SF ⊆ N × Shift × N — satisfying the five-field interface [Lean:
`SolverClosure`]:

1. *seed*: minted m ⟹ SF(m, 0, m);
2. *step-a/f/fx*: SF is closed under Definition 2's edge steps;
3. *step-mal*: SF(m,c,x) and SAlias(x,y) ⟹ SF(m,c,y), where
   SAlias(x,y) demands d-parents p,q of x,y and a *minted* witness
   origin w with SF(w,cw,p) ∧ SF(w,cw,q) (or either at ⊤) — the
   model of `joinCluster` keyed by exact (origin, shift).

If additionally every origin is minted [Lean: `origins_minted`],
then every FDeriv-derivable flow is in SF and every derivable mal is
an SAlias; in particular every grammar-accepted answer (Def. 3) is
in SF.

*Proof.* Structural induction over the FDeriv derivation. The flow
cases re-play each grammar step through the corresponding closure
field, generalized to arbitrary re-rooting (the induction carries
"for every minted m and prefix shift c₀: SF(m,c₀,z) implies
SF(m, c₀⊕c, x)", so derivations compose). The R-Join cases are where
`origins_minted` is load-bearing: the grammar's join witness z is an
origin by rootedness [Lean: `fderiv_flow_origin`], hence minted,
hence seeded, hence its two premise flows land in SF by the induction
hypothesis — producing exactly the SAlias witness. ∎

Two remarks the reader needs. First, the theorem quantifies over an
*interface*, not over our code: it holds for any relation with these
closure properties, which is what makes it dischargeable against an
implementation by *checking* the properties (§4). Second, the
direction: for a may-analysis, *soundness of the answer set* is
*completeness of the solver* relative to the reference — the solver
must find at least everything derivable.

**Theorem 1b (least-closure equivalence).** [Lean:
`sderiv_sound_fderiv`, `sderiv_iff_fderiv`] The converse holds for
the *least* closure: with no carried base and minted ⊆ origins,
every solver fact is a grammar flow — so at minted = origins the
least solver closure and the rooted grammar derive exactly the same
flows. (An arbitrary closed state has no upper bound — the universal
relation satisfies the interface — which is why the equivalence is
stated for the least closure, and why extra implementation roots
beyond the origins are a widening, not an equivalence.)

**Theorem 1c (surgical seed policy).** [Lean: `pol_solver_complete`,
`pol_answers_complete`] The surgical mode mints non-nexus origins at
the wildcard plane, which violates the zero-seed interface as
written. Parameterizing by a per-root policy (exact vs widened) and
abstracting a widened root's shifts to ⊤, every grammar-derivable
flow appears at its policy-abstracted shift — and since answer
acceptance {0, ⊤} is closed under the abstraction, a widened
function root still reports every grammar answer. This is the
theorem behind "wildcard minting is answer-complete for that
origin".

**Theorem 1d (residue abstraction).** [Lean: `ShiftHom`,
`fderiv_shift_hom`, `intShifts`, `zpShifts`, `natToZp`] The
production Z_P residues are a sound finite quotient of exact
offsets: derivability transfers along any shift-monoid homomorphism
(graph labels mapped), zero maps to zero, so exact-offset answers
remain residue answers; collisions only add. The exact ground truth
is modeled with signed offsets (`intShifts` — interior-pointer
arithmetic goes both directions); the unsigned quotient map is
instantiated (`natToZp`), the signed one is a named remaining
instance (GAPS.md).

**Theorem 2 (merge invariance).** [Lean: `fderiv_map`,
`fderiv_quotient`, `fderiv_mono`] Derivability is preserved by (i)
any node quotient — every class-merging step the solver performs
(presolve copy/field unification, dynamic a-SCC collapse,
cell-cluster union-find merges) is a graph homomorphism, and mapped
judgments remain derivable in the quotient graph; and (ii) any edge
growth — the outer resolution loop (resolve icalls → wire callee
edges → re-solve) only adds edges, so earlier derivations survive
every round.

**Theorem 3 (staging exactness).** The resource-bounding machinery
computes the *same closure*, not an approximation of it:

- **(a) Lazy minting / catch-up** [Lean: `sderiv_catchup`]: draining
  to the least closure over restricted roots m₁, then minting up to
  m₂ ⊇ m₁ and continuing from the reached facts, yields *exactly*
  the from-scratch closure over m₂ (an iff). Seeding order is
  irrelevant to a least fixpoint. Necessity of the catch-up round is
  also machine-checked [Lean: `answer_not_derivable_restricted`]: a
  seven-node counterexample where an unminted witness origin loses a
  grammar-derivable answer — the shape of the −5,737-pair
  whole-kernel deficit that refuted the "propagation loops suffice"
  conjecture.
- **(b) Batched solving** [Lean: `batched_exact` =
  `wderiv_sound` + `wderiv_complete`]: model one batch as the
  closure WDeriv over its own roots, with joins licensed by a shared
  witness table W instead of batch-local facts. If W is *sound*
  (every entry is in the eager closure) and *closed* (every batch's
  derivable facts are in W — the stable round's state), then the
  union of per-batch closures *equals* the eager closure (an iff).
  Completeness rides on a structural fact worth stating in prose: a
  fact's derivation only ever propagates its own origin — foreign
  origins enter only as join *witnesses*, which the table supplies —
  so origin batching is the right decomposition axis, formally.
  Worker interleaving, event-replay order, and spill mechanics live
  below this abstraction: they change which sound tables appear
  before stabilization, never the stable answer.
- **(c) Spill/restore** [Lean: `wderiv_restore`]: re-draining a batch
  from its spilled fixpoint (computed against an earlier table W₁)
  under a grown table W₂ ⊇ W₁ lands exactly on the fresh drain
  against W₂ (an iff). Tables only grow across rounds, so
  restore-and-continue is exact.

Theorems 3(a–c) are equivalences, not implications: the staged modes
are *exact*, which is why the implementation can (and does) demand
byte-identical answers across every mode combination as a regression
gate rather than tolerating drift.

## 4. Discharging the hypotheses per run

Theorem 1's hypotheses are properties of a finished solver state, so
each production run checks them on its own final state:

| Hypothesis | Discharged by |
|---|---|
| closure fields (step-a/f/fx, step-mal) | `--cfl-verify-closure` C0–C5: one full non-delta scan of every propagation/join/bridge rule over the final planes, asserting none still fires |
| seed presence | certificate C6: every minted root's seed fact survives in the final planes under its mint policy (exact at 0, widened at ⊤) |
| `origins_minted` | certificate C7: the origin criterion re-checked against the FINAL quotient (every origin-bearing or in-edge-less class is minted, intentionally-pruned bidi-irrelevant origins excepted); the two historical violations would both have fired here |
| Thm 3(b)'s "sound + closed table" | rounds repeat until the retained witness state is stable — no new merges, mints, OR cluster keys — matching the theorem's table-closure hypothesis; soundness holds inductively from the empty table via `wderiv_sound` |
| A3 termination | monotone growth over finite universes; an outer fixpoint that would hit its iteration cap before a no-change round REFUSES to emit answers (no warn-and-continue) |
| answer extraction | deterministic sort + sha256 pin; byte-compared across modes and machines |

One honest scoping note: the closure certificate cannot run under
batching (per-batch planes are released before a final scan could
see them), so batched runs are covered by the stability test and the
byte-identity gates against certified unbatched runs — the
instrument per run is stated, never implied.

The two historical violations of `origins_minted` — the July 2026
presolve-merge minting bug and the lazy-mint deficit — both
manifested as violations of a *named formal hypothesis* before they
were understood as code defects; the proof structure is what made
them diagnosable, and both are now regression-tested.

## 5. What is not proven, stated plainly

The trusted base is: A1/A2 (audited encoding + census, the only
informal layer), the Lean kernel, the closure-certificate scan
(C0–C7), and the answer extraction. Beyond that, the honest gaps
(tracked in `proof/lean/GAPS.md`):

- **Model-to-code refinement.** We do not prove the C++ constructs a
  `SolverClosure`; we check it per run. A run on which the
  certificate is not exercised (batching) is covered by the
  stability test and byte-identity gates against certified
  configurations, not by the theorem directly.
- **The precision direction, above the least closure.** Theorem 1b
  closes the equivalence for the least closure at exact seeds; what
  remains open is precision-*neutrality* of specific merges (the
  a-SCC collapse converse) and of the extra implementation roots
  (identity/no-in-edge mints beyond the origins — a widening whose
  extra facts are unquantified by the proof). The presolve component
  quotient is deliberately coarse and is measured, not proved tight.
- **The stable-table lemma.** The implementation's stop condition
  (no new merges, mints, or keys) syntactically matches the
  batching theorem's table-closure hypothesis, but the lemma
  connecting them — a single-member key insert is alias-inert and
  self-batch-closed — is argued in a code comment, not yet in Lean.
- **Event-replay fidelity and touch-window delta completeness** (the
  worker/spill engineering below Theorem 3(b)'s abstraction) are
  covered by byte-identity gates across all mode combinations, not
  by Lean.
- **The signed residue instance.** `fderiv_shift_hom` is proved for
  any homomorphism and instantiated for the unsigned quotient
  (`natToZp`); the signed normalization the implementation uses
  (`((o % P) + P) % P` over `intShifts`) is a pending instance.
- **Reported-answer semantics.** Identity channels, transfer
  summaries, and post-filters transform answers outside the formal
  relation; their soundness rides on the per-family completeness
  contracts and closedness certificates (§3.3), not on this proof. A
  formal `ReportedAnswer` with channel/fallback cases is future
  work.

The rooted grammar itself encodes one semantic decision reviewers
should see: FDeriv seeds flows only at origins, so store/load cycles
with no originating value (φ-cycles, entry-less loops) derive
nothing. Pairwise-saturation formulations admit such unrooted apexes
and over-approximate exactly there; rooting is both the honest
runtime semantics (an unrooted witness is an undef value) and what
makes `origins_minted` a dischargeable obligation.

---

## Notes for the writer (not part of the section)

- Body/appendix split: the claim, the layer diagram, Theorem 1 +
  both remarks, and §4's table go in §3.2; Definitions' rule figure,
  Theorems 2–3 statements, and §5 go to an appendix if space is
  tight — but keep §5 somewhere; it is a reviewer-disarming section.
- Cross-refs: §2.2 census (A1/A2 enforcement), §3.1 (batching/spill
  machinery that Thm 3 licenses), §3.3 (−N/+0 certifications that
  own the precision direction), Table T3 falsifications
  (`answer_not_derivable_restricted` pairs with the lazy-mint
  refutation entry).
- Lean file is `proof/lean/CompositionalCFL/FlowsTo.lean` (toolchain
  tracks `stable`, builds clean at 4.33.0, no sorry/axioms);
  `batched_answers_complete` is the end-to-end composition if a
  single citable theorem name is wanted. Post-review additions
  (2026-08-11): `sderiv_sound_fderiv`/`sderiv_iff_fderiv`,
  `pol_solver_complete`/`pol_answers_complete`, `ShiftHom`/
  `fderiv_shift_hom`/`intShifts`/`zpShifts`/`natToZp`, and the
  `Core.lean` `boundary_sound` same-present-symbol fix.
- The compositional-mode Lean development (Core.lean) is a separate
  older track with its own gaps — do not conflate; this section is
  about the flows-to solver only.
- Certificate block verified: `CallGraph.cc:5768-5856` (~90 lines,
  rules C0…; strip the source line refs for submission).
