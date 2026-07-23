import CompositionalCFL.Core

/-!
# Flows-to (ORCFL) soundness schema

Models the answer-anchored flows-to solver (`runFlowsToResolution`) against a
declarative shift-indexed field grammar, replacing pairwise V saturation:

- Facts are `(origin root, net field shift)` pairs; shifts live in a
  commutative monoid `S` (byte offsets; the production `Z_P` residue bucketing
  is a monoid quotient of it) extended with an absorbing unknown `⊤`
  (`Option S` with `none = ⊤`), produced by `fx` wildcard edges.
- Declarative judgment `FDeriv`, ROOTED at `origin` nodes:
  `flow z c x` — a value originating at `z` reaches `x` with net shift `c`
  (steps: `a` shift-preserving, `f r` adds `r`, `fx` absorbs to `⊤`, and
  memory hops through `mal`);
  `mal cx cy` — cells alias (M ::= -d V d | -d VX d): their parent pointers
  carry a common origin at the SAME shift (V), or either side at `⊤` (VX).
- Solver abstraction `SolverModel`: fact relation `SF` rooted at MINTED nodes
  only, closed under the propagation steps and cluster joins (`SAlias`).

Main theorem `solver_complete`: if minting covers ORIGINS (`origins_minted`),
the solver derives every grammar-derivable fact and alias. The July 2026
minting bug (presolve merges left alloca classes unminted, silently erasing
object identity) is exactly a violation of `origins_minted`. Rooting the
grammar at origins (instead of `flow_refl` at every node) is both the honest
runtime semantics — unrooted witnesses are undef values — and what makes the
minting obligation dischargeable: pairwise saturation solvers admit unrooted
valley apexes (φ-cycles, entry-less store/load loops) and thus legitimately
over-approximate flows-to on such patterns.
-/

namespace FlowsToCFL

open CompositionalCFL (Set)

/-- Commutative-enough shift monoid: exact net field offsets. The production
`Z_P` bucketing (`offset mod P`) is a quotient instance; `Nat` byte offsets
are the ground-truth instance (`natShifts`). -/
structure ShiftMonoid where
  S : Type
  add : S → S → S
  zero : S
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a

/-- Ground-truth instance: unbounded byte offsets. -/
def natShifts : ShiftMonoid where
  S := Nat
  add := Nat.add
  zero := 0
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero

/-- A shift is an exact monoid element or the absorbing unknown `⊤`
(from `fx` wildcard edges). -/
abbrev Shift (M : ShiftMonoid) := Option M.S

/-- Shift composition: exact shifts add; `⊤` absorbs. -/
def shiftComp (M : ShiftMonoid) : Shift M → Shift M → Shift M
  | some a, some b => some (M.add a b)
  | _, _ => none

theorem shiftComp_zero_right (M : ShiftMonoid) (c : Shift M) :
    shiftComp M c (some M.zero) = c := by
  cases c with
  | none => rfl
  | some a => simp [shiftComp, M.add_zero]

theorem shiftComp_zero_left (M : ShiftMonoid) (c : Shift M) :
    shiftComp M (some M.zero) c = c := by
  cases c with
  | none => rfl
  | some a => simp [shiftComp, M.zero_add]

theorem shiftComp_none_right (M : ShiftMonoid) (c : Shift M) :
    shiftComp M c none = none := by
  cases c <;> rfl

theorem shiftComp_assoc (M : ShiftMonoid) (a b c : Shift M) :
    shiftComp M (shiftComp M a b) c = shiftComp M a (shiftComp M b c) := by
  cases a <;> cases b <;> cases c <;> simp [shiftComp, M.add_assoc]

/-- Edge labels of the flows-to encoding (forward orientation only; the
implementation's inverse labels are redundant mirrors for the solver). -/
inductive FLabel (S : Type) where
  | a          -- assignment / copy (shift-preserving)
  | d          -- dereference: pointer to its memory cell
  | f (r : S)  -- field step adding residue r
  | fx         -- unknown-offset field step (wildcard, absorbs to ⊤)

/-- Labeled edge over shift carrier `S`. -/
structure FEdge (N S : Type) where
  src : N
  lbl : FLabel S
  dst : N

/-- Graph = set of labeled edges. -/
abbrev FGraph (N S : Type) := Set (FEdge N S)

/-- Judgment forms of the declarative system. -/
inductive FJudg (N S : Type) where
  | flow (z : N) (c : Option S) (x : N)
  | mal (x y : N)

/-- Declarative shift-indexed flows-to derivations, ROOTED at `origin`
nodes (allocas / globals / functions / heap sites). -/
inductive FDeriv (M : ShiftMonoid) {N : Type} (origin : N → Prop)
    (G : FGraph N M.S) : FJudg N M.S → Prop where
  | flow_refl (z : N) (hz : origin z) :
      FDeriv M origin G (.flow z (some M.zero) z)
  | flow_a {z : N} {c : Shift M} {x y : N} :
      FDeriv M origin G (.flow z c x) →
      ({ src := x, lbl := .a, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z c y)
  | flow_f {z : N} {c : Shift M} {x y : N} {r : M.S} :
      FDeriv M origin G (.flow z c x) →
      ({ src := x, lbl := .f r, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z (shiftComp M c (some r)) y)
  | flow_fx {z : N} {c : Shift M} {x y : N} :
      FDeriv M origin G (.flow z c x) →
      ({ src := x, lbl := .fx, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z none y)
  | flow_m {z : N} {c : Shift M} {x y : N} :
      FDeriv M origin G (.flow z c x) →
      FDeriv M origin G (.mal x y) →
      FDeriv M origin G (.flow z c y)
  | mal_join {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z c p) →
      FDeriv M origin G (.flow z c q) →
      FDeriv M origin G (.mal cx cy)
  | mal_joinXL {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z none p) →
      FDeriv M origin G (.flow z c q) →
      FDeriv M origin G (.mal cx cy)
  | mal_joinXR {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M origin G (.flow z c p) →
      FDeriv M origin G (.flow z none q) →
      FDeriv M origin G (.mal cx cy)

/-- Every flow judgment is rooted: its source is an origin. -/
theorem fderiv_flow_origin
    (M : ShiftMonoid) {N : Type} {origin : N → Prop} {G : FGraph N M.S} :
    ∀ {j : FJudg N M.S}, FDeriv M origin G j →
      (match j with
       | .flow z _ _ => origin z
       | .mal _ _ => True) := by
  intro j h
  induction h with
  | flow_refl z hz => exact hz
  | flow_a _ _ ih => exact ih
  | flow_f _ _ ih => exact ih
  | flow_fx _ _ ih => exact ih
  | flow_m _ _ ih₁ _ => exact ih₁
  | mal_join _ _ _ _ _ _ => trivial
  | mal_joinXL _ _ _ _ _ _ => trivial
  | mal_joinXR _ _ _ _ _ _ => trivial

/-- Edge-wise graph inclusion. -/
abbrev FGraphLe {N S : Type} (G₁ G₂ : FGraph N S) : Prop := ∀ e, e ∈ G₁ → e ∈ G₂

/-- Derivability is monotone under edge inclusion (the outer fixpoint —
resolve icalls, wire callee flows, re-solve — only ADDS edges, so earlier
derivations survive). -/
theorem fderiv_mono
    (M : ShiftMonoid) {N : Type} {origin : N → Prop} {G₁ G₂ : FGraph N M.S}
    (hSub : FGraphLe G₁ G₂) :
    ∀ {j : FJudg N M.S}, FDeriv M origin G₁ j → FDeriv M origin G₂ j := by
  intro j h
  induction h with
  | flow_refl z hz => exact FDeriv.flow_refl z hz
  | flow_a _ hE ih => exact FDeriv.flow_a ih (hSub _ hE)
  | flow_f _ hE ih => exact FDeriv.flow_f ih (hSub _ hE)
  | flow_fx _ hE ih => exact FDeriv.flow_fx ih (hSub _ hE)
  | flow_m _ _ ih₁ ih₂ => exact FDeriv.flow_m ih₁ ih₂
  | mal_join hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_join (hSub _ hEp) (hSub _ hEq) ihp ihq
  | mal_joinXL hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_joinXL (hSub _ hEp) (hSub _ hEq) ihp ihq
  | mal_joinXR hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_joinXR (hSub _ hEp) (hSub _ hEq) ihp ihq

/-- Remap an edge through a node map (labels untouched). -/
def mapFEdge {N1 N2 S : Type} (f : N1 → N2) (e : FEdge N1 S) : FEdge N2 S :=
  { src := f e.src, lbl := e.lbl, dst := f e.dst }

/-- Edge-preserving simulation. -/
def FGraphHom {N1 N2 S : Type} (f : N1 → N2)
    (G₁ : FGraph N1 S) (G₂ : FGraph N2 S) : Prop :=
  ∀ e, e ∈ G₁ → mapFEdge f e ∈ G₂

/-- Map a judgment through a node map. -/
def mapFJudg {N1 N2 S : Type} (f : N1 → N2) : FJudg N1 S → FJudg N2 S
  | .flow z c x => .flow (f z) c (f x)
  | .mal x y => .mal (f x) (f y)

/-- Simulation preserves derivability, provided origins map to origins.
This is the soundness core for every class-merging step the solver
performs: presolve copy/field merges, the in-solve dynamic a-SCC collapse,
and cell-cluster union-find merges are all node quotients, i.e. graph
homomorphisms. -/
theorem fderiv_map
    (M : ShiftMonoid) {N1 N2 : Type}
    {origin₁ : N1 → Prop} {origin₂ : N2 → Prop}
    {G₁ : FGraph N1 M.S} {G₂ : FGraph N2 M.S}
    (f : N1 → N2)
    (hHom : FGraphHom f G₁ G₂)
    (hOrigin : ∀ z, origin₁ z → origin₂ (f z)) :
    ∀ {j : FJudg N1 M.S}, FDeriv M origin₁ G₁ j →
      FDeriv M origin₂ G₂ (mapFJudg f j) := by
  intro j h
  induction h with
  | flow_refl z hz => exact FDeriv.flow_refl (f z) (hOrigin z hz)
  | flow_a _ hE ih => exact FDeriv.flow_a ih (hHom _ hE)
  | flow_f _ hE ih => exact FDeriv.flow_f ih (hHom _ hE)
  | flow_fx _ hE ih => exact FDeriv.flow_fx ih (hHom _ hE)
  | flow_m _ _ ih₁ ih₂ => exact FDeriv.flow_m ih₁ ih₂
  | mal_join hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_join (hHom _ hEp) (hHom _ hEq) ihp ihq
  | mal_joinXL hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_joinXL (hHom _ hEp) (hHom _ hEq) ihp ihq
  | mal_joinXR hEp hEq _ _ ihp ihq =>
      exact FDeriv.mal_joinXR (hHom _ hEp) (hHom _ hEq) ihp ihq

/-- Quotient graph under a node map. -/
def fquotientGraph {N Q S : Type} (G : FGraph N S) (q : N → Q) : FGraph Q S :=
  fun eQ => ∃ eN, eN ∈ G ∧ mapFEdge q eN = eQ

theorem fquotientGraph_hom {N Q S : Type} (G : FGraph N S) (q : N → Q) :
    FGraphHom q G (fquotientGraph G q) := by
  intro e hEdge
  exact ⟨e, hEdge, rfl⟩

/-- Image of the origin predicate under a quotient map. -/
def imageOrigin {N Q : Type} (origin : N → Prop) (q : N → Q) : Q → Prop :=
  fun oq => ∃ z, origin z ∧ q z = oq

/-- Quotienting (any class merge) preserves derivability. Precision-neutrality
of the a-SCC collapse (the converse direction, requiring mutual
shift-preserving reachability) is a separate, pending obligation — see
GAPS.md. -/
theorem fderiv_quotient
    (M : ShiftMonoid) {N Q : Type} {origin : N → Prop}
    (G : FGraph N M.S) (q : N → Q)
    {j : FJudg N M.S}
    (h : FDeriv M origin G j) :
    FDeriv M (imageOrigin origin q) (fquotientGraph G q) (mapFJudg q j) :=
  fderiv_map M q (fquotientGraph_hom G q)
    (fun z hz => ⟨z, hz, rfl⟩) h

/-!
## Solver abstraction: minted-root fact propagation

The implementation stores facts `(origin, shift)` only for MINTED origins and
joins cells on exact fact equality (or `⊤`). `SolverModel` captures the
closure properties of the fact relation `SF` (certified per-run by
`--cfl-verify-closure`); `origins_minted` is the minting invariant the
implementation's criterion (origin-bearing classes + no-in-edge classes +
functions) must discharge.
-/

/-- Cluster-join alias induced by the solver's fact relation: the two cells'
parent pointers carry a common minted origin at the same shift, or either
side at `⊤`. Models `joinCluster` keyed by exact `(o, s)` plus the VX
bridge/union of the `(o, ⊤)` cluster. -/
def SAlias (M : ShiftMonoid) {N : Type} (G : FGraph N M.S)
    (minted : N → Prop) (SF : N → Shift M → N → Prop)
    (cx cy : N) : Prop :=
  ∃ p q,
    ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G ∧
    ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G ∧
    ∃ m, minted m ∧
      ((∃ c, SF m c p ∧ SF m c q) ∨
       (SF m none p ∧ ∃ c, SF m c q) ∨
       ((∃ c, SF m c p) ∧ SF m none q))

/-- Closure rules alone — what one drain loop guarantees for WHATEVER root
set is currently minted (the `--cfl-verify-closure` certificate checks
exactly these fields over the final planes). Split out of `SolverModel` so
RESTRICTED minting (lazy-mint stages, task #21) is expressible: a
`SolverClosure` with `minted ⊊ origins` is a legal solver state, it just
loses the completeness theorem — see `answer_not_derivable_restricted`
below for a concrete witness of that loss. -/
structure SolverClosure (M : ShiftMonoid) {N : Type} (G : FGraph N M.S) where
  minted : N → Prop
  SF : N → Shift M → N → Prop
  seed : ∀ m, minted m → SF m (some M.zero) m
  step_a : ∀ {m : N} {c : Shift M} {x y : N},
    SF m c x →
    ({ src := x, lbl := .a, dst := y } : FEdge N M.S) ∈ G →
    SF m c y
  step_f : ∀ {m : N} {c : Shift M} {x y : N} {r : M.S},
    SF m c x →
    ({ src := x, lbl := .f r, dst := y } : FEdge N M.S) ∈ G →
    SF m (shiftComp M c (some r)) y
  step_fx : ∀ {m : N} {c : Shift M} {x y : N},
    SF m c x →
    ({ src := x, lbl := .fx, dst := y } : FEdge N M.S) ∈ G →
    SF m none y
  step_mal : ∀ {m : N} {c : Shift M} {x y : N},
    SF m c x →
    SAlias M G minted SF x y →
    SF m c y

/-- Abstract solver: closure rules PLUS the minting invariant. -/
structure SolverModel (M : ShiftMonoid) {N : Type} (origin : N → Prop)
    (G : FGraph N M.S) extends SolverClosure M G where
  /-- Minting completeness FOR ORIGINS — dischargeable: the implementation
  mints every origin-bearing class (plus no-in-edge classes and functions).
  The July 2026 minting bug (`!hasIn`-only minting after presolve merges)
  violated exactly this: an alloca class merged with in-edged nodes was
  never minted, no root reached it, and its object identity vanished.
  The July 2026 whole-kernel LAZY-MINT deficit (task #21: -5737 pairs,
  tcp_ulp / 9p-transport ops registration lists) is the second violation
  in the wild: witness origins outside the demand-driven ancestor closure
  stayed unminted. The catch-up round restores this invariant at
  convergence; `sderiv_catchup` proves that restores the full closure. -/
  origins_minted : ∀ z, origin z → minted z

/-- Completeness of the solver against the origin-rooted declarative
grammar: every grammar-derivable flow re-rooted at any minted fact is a
solver fact, and every grammar-derivable alias is a solver cluster join. -/
theorem solver_complete
    (M : ShiftMonoid) {N : Type} {origin : N → Prop} {G : FGraph N M.S}
    (SM : SolverModel M origin G) :
    ∀ {j : FJudg N M.S}, FDeriv M origin G j →
      (match j with
       | .flow z c x =>
           ∀ (m : N) (c0 : Shift M),
             SM.minted m → SM.SF m c0 z → SM.SF m (shiftComp M c0 c) x
       | .mal x y => SAlias M G SM.minted SM.SF x y) := by
  intro j h
  induction h with
  | flow_refl z hz =>
      intro m c0 _ hSF
      simpa [shiftComp_zero_right] using hSF
  | flow_a _ hE ih =>
      intro m c0 hm hSF
      exact SM.step_a (ih m c0 hm hSF) hE
  | flow_f _ hE ih =>
      intro m c0 hm hSF
      have := SM.step_f (ih m c0 hm hSF) hE
      simpa [shiftComp_assoc] using this
  | flow_fx _ hE ih =>
      intro m c0 hm hSF
      have := SM.step_fx (ih m c0 hm hSF) hE
      simpa [shiftComp_none_right] using this
  | flow_m _ _ ih₁ ih₂ =>
      intro m c0 hm hSF
      exact SM.step_mal (ih₁ m c0 hm hSF) ih₂
  | mal_join hEp hEq hp hq ihp ihq =>
      -- Re-root both matching-shift branches at the (minted) grammar
      -- origin itself; shifts are preserved exactly.
      rename_i p q cx cy z c
      have hz : origin z := fderiv_flow_origin M hp
      have hm : SM.minted z := SM.origins_minted z hz
      have hp' := ihp z (some M.zero) hm (SM.seed z hm)
      have hq' := ihq z (some M.zero) hm (SM.seed z hm)
      rw [shiftComp_zero_left] at hp' hq'
      exact ⟨p, q, hEp, hEq, z, hm, Or.inl ⟨c, hp', hq'⟩⟩
  | mal_joinXL hEp hEq hp hq ihp ihq =>
      rename_i p q cx cy z c
      have hz : origin z := fderiv_flow_origin M hp
      have hm : SM.minted z := SM.origins_minted z hz
      have hp' := ihp z (some M.zero) hm (SM.seed z hm)
      have hq' := ihq z (some M.zero) hm (SM.seed z hm)
      rw [shiftComp_zero_left] at hp' hq'
      exact ⟨p, q, hEp, hEq, z, hm, Or.inr (Or.inl ⟨hp', c, hq'⟩)⟩
  | mal_joinXR hEp hEq hp hq ihp ihq =>
      rename_i p q cx cy z c
      have hz : origin z := fderiv_flow_origin M hp
      have hm : SM.minted z := SM.origins_minted z hz
      have hp' := ihp z (some M.zero) hm (SM.seed z hm)
      have hq' := ihq z (some M.zero) hm (SM.seed z hm)
      rw [shiftComp_zero_left] at hp' hq'
      exact ⟨p, q, hEp, hEq, z, hm, Or.inr (Or.inr ⟨⟨c, hp'⟩, hq'⟩)⟩

/-- Indirect-call answer completeness: a function (an origin) whose value
flows to the fptr at shift zero (or unknown) is found by the solver.
Resolution accepts exactly these two shifts. -/
theorem answers_complete
    (M : ShiftMonoid) {N : Type} {origin : N → Prop} {G : FGraph N M.S}
    (SM : SolverModel M origin G)
    {fnode fptr : N}
    {c : Shift M}
    (hAccept : c = some M.zero ∨ c = none)
    (hReach : FDeriv M origin G (.flow fnode c fptr)) :
    SM.SF fnode c fptr := by
  have hz : origin fnode := fderiv_flow_origin M hReach
  have hm : SM.minted fnode := SM.origins_minted fnode hz
  have h := solver_complete M SM hReach fnode (some M.zero) hm
              (SM.seed fnode hm)
  cases hAccept with
  | inl h0 => subst h0; simpa [shiftComp_zero_left] using h
  | inr hTop => subst hTop; simpa [shiftComp_none_right, shiftComp_zero_left] using h

/-!
## Lazy minting (task #21): staged least closures and the catch-up theorem

The implementation's lazy mode drains to the least closure over a RESTRICTED
root set, mints more roots, drains again, and finishes with a CATCH-UP round
that mints everything still deferred. Two facts must hold:

1. `sderiv_catchup` — staging is confluent: draining restricted and then
   continuing from the reached facts with a larger root set lands EXACTLY on
   the from-scratch closure over the larger set. This is why the catch-up
   round's answers are identical to the eager solve by construction.
2. `answer_not_derivable_restricted` — the catch-up is NECESSARY:
   `origins_minted` cannot be dropped, because an unminted witness origin
   loses grammar-derivable answers (a five-node counterexample; the
   whole-kernel -5737-pair deficit is this shape at scale).
-/

/-- Empty base fact relation (a from-scratch stage). -/
def noBase (M : ShiftMonoid) (N : Type) : N → Shift M → N → Prop :=
  fun _ _ _ => False

/-- Least solver closure over root set `minted`, starting from carried-over
facts `base` (the previous stage's planes; `noBase` for stage one). Joins are
flattened into the three witness-shift cases of `SAlias` so induction stays
elementary. This is the relation one drain loop actually computes. -/
inductive SDeriv (M : ShiftMonoid) {N : Type} (G : FGraph N M.S)
    (minted : N → Prop) (base : N → Shift M → N → Prop) :
    N → Shift M → N → Prop where
  | ofBase {m : N} {c : Shift M} {x : N} :
      base m c x → SDeriv M G minted base m c x
  | seed (m : N) (hm : minted m) :
      SDeriv M G minted base m (some M.zero) m
  | step_a {m : N} {c : Shift M} {x y : N} :
      SDeriv M G minted base m c x →
      ({ src := x, lbl := .a, dst := y } : FEdge N M.S) ∈ G →
      SDeriv M G minted base m c y
  | step_f {m : N} {c : Shift M} {x y : N} {r : M.S} :
      SDeriv M G minted base m c x →
      ({ src := x, lbl := .f r, dst := y } : FEdge N M.S) ∈ G →
      SDeriv M G minted base m (shiftComp M c (some r)) y
  | step_fx {m : N} {c : Shift M} {x y : N} :
      SDeriv M G minted base m c x →
      ({ src := x, lbl := .fx, dst := y } : FEdge N M.S) ∈ G →
      SDeriv M G minted base m none y
  | join_e {m : N} {c : Shift M} {x y p q w : N} {cw : Shift M} :
      ({ src := p, lbl := .d, dst := x } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := y } : FEdge N M.S) ∈ G →
      minted w →
      SDeriv M G minted base w cw p →
      SDeriv M G minted base w cw q →
      SDeriv M G minted base m c x →
      SDeriv M G minted base m c y
  | join_xl {m : N} {c : Shift M} {x y p q w : N} {cw : Shift M} :
      ({ src := p, lbl := .d, dst := x } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := y } : FEdge N M.S) ∈ G →
      minted w →
      SDeriv M G minted base w none p →
      SDeriv M G minted base w cw q →
      SDeriv M G minted base m c x →
      SDeriv M G minted base m c y
  | join_xr {m : N} {c : Shift M} {x y p q w : N} {cw : Shift M} :
      ({ src := p, lbl := .d, dst := x } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := y } : FEdge N M.S) ∈ G →
      minted w →
      SDeriv M G minted base w cw p →
      SDeriv M G minted base w none q →
      SDeriv M G minted base m c x →
      SDeriv M G minted base m c y

/-- Monotonicity in both the root set and the carried-over base. -/
theorem sderiv_mono (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {m₁ m₂ : N → Prop} {b₁ b₂ : N → Shift M → N → Prop}
    (hm : ∀ n, m₁ n → m₂ n)
    (hb : ∀ m c x, b₁ m c x → b₂ m c x) :
    ∀ {m : N} {c : Shift M} {x : N},
      SDeriv M G m₁ b₁ m c x → SDeriv M G m₂ b₂ m c x := by
  intro m c x h
  induction h with
  | ofBase hB => exact .ofBase (hb _ _ _ hB)
  | seed n hn => exact .seed n (hm n hn)
  | step_a _ hE ih => exact .step_a ih hE
  | step_f _ hE ih => exact .step_f ih hE
  | step_fx _ hE ih => exact .step_fx ih hE
  | join_e hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_e hEp hEq (hm _ hw) ihp ihq ihx
  | join_xl hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_xl hEp hEq (hm _ hw) ihp ihq ihx
  | join_xr hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_xr hEp hEq (hm _ hw) ihp ihq ihx

/-- Flattening: re-deriving over an already-derived base adds nothing
(the monad-join law of the closure). -/
theorem sderiv_bind (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {base : N → Shift M → N → Prop} :
    ∀ {m : N} {c : Shift M} {x : N},
      SDeriv M G minted (SDeriv M G minted base) m c x →
      SDeriv M G minted base m c x := by
  intro m c x h
  induction h with
  | ofBase hB => exact hB
  | seed n hn => exact .seed n hn
  | step_a _ hE ih => exact .step_a ih hE
  | step_f _ hE ih => exact .step_f ih hE
  | step_fx _ hE ih => exact .step_fx ih hE
  | join_e hEp hEq hw _ _ _ ihp ihq ihx => exact .join_e hEp hEq hw ihp ihq ihx
  | join_xl hEp hEq hw _ _ _ ihp ihq ihx => exact .join_xl hEp hEq hw ihp ihq ihx
  | join_xr hEp hEq hw _ _ _ ihp ihq ihx => exact .join_xr hEp hEq hw ihp ihq ihx

/-- CATCH-UP CONFLUENCE (task #21, the exactness theorem behind commit
446f35b): drain to the closure over restricted roots `m₁`, then mint up to
`m₂ ⊇ m₁` and continue draining from the reached facts — the result is
EXACTLY the from-scratch closure over `m₂`. Seeding order is irrelevant to
the least fixpoint, so the staged (lazy + catch-up) solve returns the eager
answers by construction; no soundness argument about WHICH roots the lazy
stages picked is needed. -/
theorem sderiv_catchup (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {m₁ m₂ : N → Prop} {base : N → Shift M → N → Prop}
    (h12 : ∀ n, m₁ n → m₂ n)
    {m : N} {c : Shift M} {x : N} :
    SDeriv M G m₂ (SDeriv M G m₁ base) m c x ↔ SDeriv M G m₂ base m c x := by
  constructor
  · intro h
    exact sderiv_bind M
      (sderiv_mono M (fun n hn => hn)
        (fun m c x hB => sderiv_mono M h12 (fun _ _ _ hb => hb) hB) h)
  · intro h
    exact sderiv_mono M (fun n hn => hn)
      (fun m c x hB => SDeriv.ofBase hB) h

/-- `SDeriv` is the LEAST closure: it embeds into any `SolverClosure`
containing its roots and base. Used both to transfer completeness and to
prove NON-derivability by exhibiting a small closed relation. -/
theorem sderiv_le_closure (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {base : N → Shift M → N → Prop}
    (C : SolverClosure M G)
    (hm : ∀ n, minted n → C.minted n)
    (hb : ∀ m c x, base m c x → C.SF m c x) :
    ∀ {m : N} {c : Shift M} {x : N},
      SDeriv M G minted base m c x → C.SF m c x := by
  intro m c x h
  induction h with
  | ofBase hB => exact hb _ _ _ hB
  | seed n hn => exact C.seed n (hm n hn)
  | step_a _ hE ih => exact C.step_a ih hE
  | step_f _ hE ih => exact C.step_f ih hE
  | step_fx _ hE ih => exact C.step_fx ih hE
  | join_e hEp hEq hw _ _ _ ihp ihq ihx =>
      exact C.step_mal ihx ⟨_, _, hEp, hEq, _, hm _ hw, Or.inl ⟨_, ihp, ihq⟩⟩
  | join_xl hEp hEq hw _ _ _ ihp ihq ihx =>
      exact C.step_mal ihx
        ⟨_, _, hEp, hEq, _, hm _ hw, Or.inr (Or.inl ⟨ihp, _, ihq⟩)⟩
  | join_xr hEp hEq hw _ _ _ ihp ihq ihx =>
      exact C.step_mal ihx
        ⟨_, _, hEp, hEq, _, hm _ hw, Or.inr (Or.inr ⟨⟨_, ihp⟩, ihq⟩)⟩

/-- The least closure is itself a `SolverClosure`. -/
def sderivClosure (M : ShiftMonoid) {N : Type} (G : FGraph N M.S)
    (minted : N → Prop) : SolverClosure M G where
  minted := minted
  SF := SDeriv M G minted (noBase M N)
  seed := fun m hm => .seed m hm
  step_a := fun h hE => .step_a h hE
  step_f := fun h hE => .step_f h hE
  step_fx := fun h hE => .step_fx h hE
  step_mal := fun h hAl => by
    obtain ⟨p, q, hEp, hEq, w, hw, hDisj⟩ := hAl
    rcases hDisj with ⟨cw, hp, hq⟩ | ⟨hp, cw, hq⟩ | ⟨⟨cw, hp⟩, hq⟩
    · exact .join_e hEp hEq hw hp hq h
    · exact .join_xl hEp hEq hw hp hq h
    · exact .join_xr hEp hEq hw hp hq h

/-- End-to-end exactness of the staged solve: run the lazy stage over ANY
restricted root set `m₁`, catch up to `m₂` covering the origins, keep
draining — every grammar-accepted answer is in the final planes. -/
theorem catchup_answers_complete (M : ShiftMonoid) {N : Type}
    {origin : N → Prop} {G : FGraph N M.S} {m₁ m₂ : N → Prop}
    (h12 : ∀ n, m₁ n → m₂ n)
    (hOrig : ∀ z, origin z → m₂ z)
    {fnode fptr : N} {c : Shift M}
    (hAccept : c = some M.zero ∨ c = none)
    (hReach : FDeriv M origin G (.flow fnode c fptr)) :
    SDeriv M G m₂ (SDeriv M G m₁ (noBase M N)) fnode c fptr := by
  rw [sderiv_catchup M h12]
  exact answers_complete M
    (SM := { toSolverClosure := sderivClosure M G m₂, origins_minted := hOrig })
    hAccept hReach

/-!
## Necessity of the catch-up: restricted minting loses answers

Five-node counterexample (field-insensitive): function `fn` is stored
through pointer `pp` (cell `cs`) and loaded through pointer `qq` (cell
`cl`) into the fptr; the aliasing witness is origin `ww`, which flows to
both pointers. Minting only `fn` — a strict subset of the origins — the
least closure never fires the join and the answer `fn ⟶ fp` is lost,
while the declarative grammar derives it. So `origins_minted` cannot be
weakened to any root set missing a live witness: a lazy stage must either
prove its deferred origins are dead or catch them up before answering.
(The whole-kernel deficit — tcp_ulp / 9p ops registration chains,
-5737 pairs — is this shape reached through circular list structure.) -/
namespace CounterExample

inductive CE where
  | fn | ww | pp | qq | cs | cl | fp
  deriving DecidableEq, Repr

open CE

/-- Edges: `ww →a pp`, `ww →a qq` (witness reaches both pointers),
`pp →d cs`, `qq →d cl` (store/load cells), `fn →a cs` (store),
`cl →a fp` (load feeds the fptr). -/
def G : FGraph CE Nat := fun e =>
  e = ⟨ww, .a, pp⟩ ∨ e = ⟨ww, .a, qq⟩ ∨ e = ⟨pp, .d, cs⟩ ∨
  e = ⟨qq, .d, cl⟩ ∨ e = ⟨fn, .a, cs⟩ ∨ e = ⟨cl, .a, fp⟩

def origin : CE → Prop := fun n => n = fn ∨ n = ww

/-- Convenience: the six edges of `G` as membership facts. -/
theorem eWP : ({ src := ww, lbl := .a, dst := pp } : FEdge CE Nat) ∈ G :=
  Or.inl rfl
theorem eWQ : ({ src := ww, lbl := .a, dst := qq } : FEdge CE Nat) ∈ G :=
  Or.inr (Or.inl rfl)
theorem ePD : ({ src := pp, lbl := .d, dst := cs } : FEdge CE Nat) ∈ G :=
  Or.inr (Or.inr (Or.inl rfl))
theorem eQD : ({ src := qq, lbl := .d, dst := cl } : FEdge CE Nat) ∈ G :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem eFS : ({ src := fn, lbl := .a, dst := cs } : FEdge CE Nat) ∈ G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem eLF : ({ src := cl, lbl := .a, dst := fp } : FEdge CE Nat) ∈ G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The grammar derives the answer: `fn` flows to `fp` at shift zero. -/
theorem answer_derivable :
    FDeriv natShifts origin G (.flow fn (some natShifts.zero) fp) := by
  have hfn : FDeriv natShifts origin G (.flow fn (some natShifts.zero) cs) :=
    .flow_a (.flow_refl fn (Or.inl rfl)) eFS
  have hwp : FDeriv natShifts origin G (.flow ww (some natShifts.zero) pp) :=
    .flow_a (.flow_refl ww (Or.inr rfl)) eWP
  have hwq : FDeriv natShifts origin G (.flow ww (some natShifts.zero) qq) :=
    .flow_a (.flow_refl ww (Or.inr rfl)) eWQ
  have hmal : FDeriv natShifts origin G (.mal cs cl) :=
    .mal_join ePD eQD hwp hwq
  exact .flow_a (.flow_m hfn hmal) eLF

/-- With full minting the solver finds it (sanity control). -/
theorem answer_derivable_full :
    SDeriv natShifts G origin (noBase natShifts CE)
      fn (some natShifts.zero) fp :=
  answers_complete natShifts
    (SM := { toSolverClosure := sderivClosure natShifts G origin,
             origins_minted := fun _ hz => hz })
    (Or.inl rfl) answer_derivable

/-- A closed relation over minted = {fn} that lacks the answer: `fn`'s
facts reach only `fn` and `cs`; no minted witness ever reaches both
pointers, so no join fires. -/
def blockedSF : CE → Shift natShifts → CE → Prop :=
  fun m c x => m = fn ∧ c = some natShifts.zero ∧ (x = fn ∨ x = cs)

def blockedClosure : SolverClosure natShifts G where
  minted := fun n => n = fn
  SF := blockedSF
  seed := fun m hm => ⟨hm, rfl, Or.inl hm⟩
  step_a := by
    rintro m c x y ⟨hm, hc, hx⟩ hE
    rcases hE with h | h | h | h | h | h
    · -- ww →a pp : source ww carries no blocked fact
      injection h with h1 h2 h3
      subst h1
      rcases hx with hx | hx <;> exact absurd hx (by decide)
    · injection h with h1 h2 h3
      subst h1
      rcases hx with hx | hx <;> exact absurd hx (by decide)
    · -- pp →d cs : label mismatch
      injection h with h1 h2 h3
      cases h2
    · injection h with h1 h2 h3
      cases h2
    · -- fn →a cs : the one real propagation
      injection h with h1 h2 h3
      subst h3
      exact ⟨hm, hc, Or.inr rfl⟩
    · -- cl →a fp : source cl carries no blocked fact
      injection h with h1 h2 h3
      subst h1
      rcases hx with hx | hx <;> exact absurd hx (by decide)
  step_f := by
    rintro m c x y r ⟨_, _, _⟩ hE
    rcases hE with h | h | h | h | h | h <;>
      (injection h with h1 h2 h3; cases h2)
  step_fx := by
    rintro m c x y ⟨_, _, _⟩ hE
    rcases hE with h | h | h | h | h | h <;>
      (injection h with h1 h2 h3; cases h2)
  step_mal := by
    rintro m c x y hSF ⟨p', q', hEp, hEq, w', hw', hDisj⟩
    subst hw'
    exfalso
    -- every disjunct puts a blocked fact of fn at p'; extract where p' is
    have hpx : p' = fn ∨ p' = cs := by
      rcases hDisj with ⟨cw, hp, _⟩ | ⟨hp, _⟩ | ⟨⟨cw, hp⟩, _⟩
      · exact hp.2.2
      · exact absurd hp.2.1 (by simp)
      · exact hp.2.2
    -- but a join parent must own a d-edge, i.e. be pp or qq
    rcases hEp with h | h | h | h | h | h
    · injection h with h1 h2 h3; cases h2
    · injection h with h1 h2 h3; cases h2
    · injection h with h1 h2 h3
      subst h1
      rcases hpx with hx | hx <;> exact absurd hx (by decide)
    · injection h with h1 h2 h3
      subst h1
      rcases hpx with hx | hx <;> exact absurd hx (by decide)
    · injection h with h1 h2 h3; cases h2
    · injection h with h1 h2 h3; cases h2

/-- THE NECESSITY THEOREM: minting only `fn` (a strict subset of the
origins — the witness `ww` stays deferred), the least solver closure does
NOT derive the grammar-derivable answer. `origins_minted` is load-bearing;
a lazy solve that never catches up is incomplete. -/
theorem answer_not_derivable_restricted :
    ¬ SDeriv natShifts G (fun n => n = fn) (noBase natShifts CE)
        fn (some natShifts.zero) fp := by
  intro h
  have hIn : blockedSF fn (some natShifts.zero) fp :=
    sderiv_le_closure natShifts (minted := fun n => n = fn)
      (base := noBase natShifts CE) blockedClosure
      (fun n hn => hn) (fun _ _ _ hB => hB.elim) h
  rcases hIn with ⟨_, _, hx | hx⟩ <;> exact absurd hx (by decide)

end CounterExample

end FlowsToCFL
