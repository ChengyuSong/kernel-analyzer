import CompositionalCFL.Core

/-!
# Flows-to (ORCFL) soundness schema

Models the answer-anchored flows-to solver (`runFlowsToResolution`) against a
declarative shift-indexed field grammar, replacing pairwise V saturation:

- Facts are `(origin root, net field shift)` pairs; shifts live in a
  commutative monoid `S` (byte offsets; the production `Z_P` residue bucketing
  is a monoid quotient of it) extended with an absorbing unknown `⊤`
  (`Option S` with `none = ⊤`), produced by `fx` wildcard edges.
- Declarative judgment `FDeriv`:
  `flow z c x` — a value originating at `z` reaches `x` with net shift `c`
  (steps: `a` shift-preserving, `f r` adds `r`, `fx` absorbs to `⊤`, and
  memory hops through `mal`);
  `mal cx cy` — cells alias (M ::= -d V d | -d VX d): their parent pointers
  carry a common origin at the SAME shift (V), or either side at `⊤` (VX).
- Solver abstraction `SolverModel`: fact relation `SF` rooted at MINTED nodes
  only, closed under the propagation steps and cluster joins (`SAlias`).

Main theorem `solver_complete`: if minting COVERS the graph (every node is
reached by some minted root), the solver derives every grammar-derivable
fact and alias. The July 2026 minting bug (presolve merges left alloca
classes unminted, silently erasing object identity) is exactly a violation
of the `coverage` hypothesis — `answers_complete` fails without it.
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

/-- Declarative shift-indexed flows-to derivations. -/
inductive FDeriv (M : ShiftMonoid) {N : Type} (G : FGraph N M.S) :
    FJudg N M.S → Prop where
  | flow_refl (z : N) :
      FDeriv M G (.flow z (some M.zero) z)
  | flow_a {z : N} {c : Shift M} {x y : N} :
      FDeriv M G (.flow z c x) →
      ({ src := x, lbl := .a, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z c y)
  | flow_f {z : N} {c : Shift M} {x y : N} {r : M.S} :
      FDeriv M G (.flow z c x) →
      ({ src := x, lbl := .f r, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z (shiftComp M c (some r)) y)
  | flow_fx {z : N} {c : Shift M} {x y : N} :
      FDeriv M G (.flow z c x) →
      ({ src := x, lbl := .fx, dst := y } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z none y)
  | flow_m {z : N} {c : Shift M} {x y : N} :
      FDeriv M G (.flow z c x) →
      FDeriv M G (.mal x y) →
      FDeriv M G (.flow z c y)
  | mal_join {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z c p) →
      FDeriv M G (.flow z c q) →
      FDeriv M G (.mal cx cy)
  | mal_joinXL {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z none p) →
      FDeriv M G (.flow z c q) →
      FDeriv M G (.mal cx cy)
  | mal_joinXR {p q cx cy : N} {z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : FEdge N M.S) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : FEdge N M.S) ∈ G →
      FDeriv M G (.flow z c p) →
      FDeriv M G (.flow z none q) →
      FDeriv M G (.mal cx cy)

/-- Edge-wise graph inclusion. -/
abbrev FGraphLe {N S : Type} (G₁ G₂ : FGraph N S) : Prop := ∀ e, e ∈ G₁ → e ∈ G₂

/-- Derivability is monotone under edge inclusion (the outer fixpoint —
resolve icalls, wire callee flows, re-solve — only ADDS edges, so earlier
derivations survive). -/
theorem fderiv_mono
    (M : ShiftMonoid) {N : Type} {G₁ G₂ : FGraph N M.S}
    (hSub : FGraphLe G₁ G₂) :
    ∀ {j : FJudg N M.S}, FDeriv M G₁ j → FDeriv M G₂ j := by
  intro j h
  induction h with
  | flow_refl z => exact FDeriv.flow_refl z
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

/-- Simulation preserves derivability. This is the soundness core for every
class-merging step the solver performs: presolve copy/field merges, the
in-solve dynamic a-SCC collapse, and cell-cluster union-find merges are all
node quotients, i.e. graph homomorphisms. -/
theorem fderiv_map
    (M : ShiftMonoid) {N1 N2 : Type}
    {G₁ : FGraph N1 M.S} {G₂ : FGraph N2 M.S}
    (f : N1 → N2)
    (hHom : FGraphHom f G₁ G₂) :
    ∀ {j : FJudg N1 M.S}, FDeriv M G₁ j → FDeriv M G₂ (mapFJudg f j) := by
  intro j h
  induction h with
  | flow_refl z => exact FDeriv.flow_refl (f z)
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

/-- Quotienting (any class merge) preserves derivability. Precision-neutrality
of the a-SCC collapse (the converse direction, requiring mutual
shift-preserving reachability) is a separate, pending obligation — see
GAPS.md. -/
theorem fderiv_quotient
    (M : ShiftMonoid) {N Q : Type}
    (G : FGraph N M.S) (q : N → Q)
    {j : FJudg N M.S}
    (h : FDeriv M G j) :
    FDeriv M (fquotientGraph G q) (mapFJudg q j) :=
  fderiv_map M q (fquotientGraph_hom G q) h

/-!
## Solver abstraction: minted-root fact propagation

The implementation stores facts `(origin, shift)` only for MINTED origins and
joins cells on exact fact equality (or `⊤`). `SolverModel` captures the
closure properties of the fact relation `SF`; `coverage` is the minting
completeness invariant.
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

/-- Abstract solver: minted roots, fact relation, closure under the
propagation rules, and the minting-coverage invariant. -/
structure SolverModel (M : ShiftMonoid) {N : Type} (G : FGraph N M.S) where
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
  /-- Minting completeness: every node is reached by some minted root.
  The July 2026 minting bug (`!hasIn`-only minting after presolve merges)
  violated exactly this — an alloca class merged with in-edged nodes was
  never minted, no root reached it, and its object identity vanished. -/
  coverage : ∀ z : N, ∃ m c, minted m ∧ SF m c z

/-- Completeness of the solver against the declarative grammar, given
coverage: every grammar-derivable flow re-rooted at any minted fact is a
solver fact, and every grammar-derivable alias is a solver cluster join. -/
theorem solver_complete
    (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    (SM : SolverModel M G) :
    ∀ {j : FJudg N M.S}, FDeriv M G j →
      (match j with
       | .flow z c x =>
           ∀ (m : N) (c0 : Shift M),
             SM.minted m → SM.SF m c0 z → SM.SF m (shiftComp M c0 c) x
       | .mal x y => SAlias M G SM.minted SM.SF x y) := by
  intro j h
  induction h with
  | flow_refl z =>
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
      -- Re-root the two matching-shift branches at a minted witness
      -- covering the grammar's origin z; shifts stay equal.
      rename_i p q cx cy z c
      obtain ⟨m, c0, hm, hSF⟩ := SM.coverage z
      refine ⟨p, q, hEp, hEq, m, hm, Or.inl ⟨shiftComp M c0 c, ?_, ?_⟩⟩
      · exact ihp m c0 hm hSF
      · exact ihq m c0 hm hSF
  | mal_joinXL hEp hEq hp hq ihp ihq =>
      rename_i p q cx cy z c
      obtain ⟨m, c0, hm, hSF⟩ := SM.coverage z
      have hp' := ihp m c0 hm hSF
      have hq' := ihq m c0 hm hSF
      rw [shiftComp_none_right] at hp'
      exact ⟨p, q, hEp, hEq, m, hm,
             Or.inr (Or.inl ⟨hp', shiftComp M c0 c, hq'⟩)⟩
  | mal_joinXR hEp hEq hp hq ihp ihq =>
      rename_i p q cx cy z c
      obtain ⟨m, c0, hm, hSF⟩ := SM.coverage z
      have hp' := ihp m c0 hm hSF
      have hq' := ihq m c0 hm hSF
      rw [shiftComp_none_right] at hq'
      exact ⟨p, q, hEp, hEq, m, hm,
             Or.inr (Or.inr ⟨⟨shiftComp M c0 c, hp'⟩, hq'⟩)⟩

/-- Indirect-call answer completeness: a function whose value flows to the
fptr at shift zero (or unknown) is found by the solver, provided function
nodes are minted (they are, unconditionally, in the implementation) and
coverage holds. Resolution accepts exactly these two shifts. -/
theorem answers_complete
    (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    (SM : SolverModel M G)
    {fnode fptr : N}
    (hFuncMinted : SM.minted fnode)
    {c : Shift M}
    (hAccept : c = some M.zero ∨ c = none)
    (hReach : FDeriv M G (.flow fnode c fptr)) :
    SM.SF fnode c fptr := by
  have h := solver_complete M SM hReach fnode (some M.zero) hFuncMinted
              (SM.seed fnode hFuncMinted)
  cases hAccept with
  | inl h0 => subst h0; simpa [shiftComp_zero_left] using h
  | inr hTop => subst hTop; simpa [shiftComp_none_right, shiftComp_zero_left] using h

end FlowsToCFL
