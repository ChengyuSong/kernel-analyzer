import CompositionalCFL.NamedCells

/-!
# Type labels: lazy object identity from initialization

Plan `docs/plan-named-cells.md` 3.9. An allocation site produces bytes;
the program gives them a type when it first writes them as a struct.
The label is minted there and travels with the origin: a fact `base z`
(an object of site `z` not yet seen initialized) crossing a labeling
point `lab t` (the object's first typed write, as struct `t`) becomes
`lab z t` downstream. Cell clusters are keyed by the labeled origin, so
objects of one site with different labels are different objects. A
plain `base z` is the WILDCARD label: a pointer that reached the object
without crossing a labeling point may touch any instance, so `base z`
meets every `lab z t` (the label analogue of the VX bridge between the
wildcard shift and the exact shifts). A fact already labeled passes a
labeling point unchanged (decision 3.9: keep, and let the rule check
report a second init).

Model.
- `LDeriv`: the flows-to grammar with relabel edges, labeled origins,
  and joins that require `meets`.
- `RDeriv`: the exact reference over concrete INSTANCES `(z, l)`: an
  object of site `z` whose initialization labeled it `l` (`none`: never
  initialized through a labeling point). A store and a load meet iff
  their pointers hold the same instance at the same offset. The
  reference encodes the one condition labels rest on, FAITHFULNESS: only
  instances initialized as `t` pass a `lab t` edge. A labeling point is
  an instance's first typed write; an instance passing it already
  initialized otherwise is memory reused for another type, which the
  program can only observe through a stale pointer (use after reuse).

Results.
- `label_sound`: every concrete flow of `RDeriv` is covered by `LDeriv`,
  through the instance's plain origin or its own label; every concrete
  cell alias is an `LDeriv` alias.
- `label_removal_only`: erasing labels (relabel edges become `a`,
  labeled origins their site) maps every `LDeriv` derivation onto
  today's `FDeriv`: labels only remove answers.
-/

namespace TypeLabels

open CompositionalCFL (Set)
open FlowsToCFL
open NamedCells (covers covers_comp)

inductive LLabel (S T : Type) where
  | a
  | d
  | f (r : S)
  | fx
  /-- a labeling point: the object's first typed write, as struct `t` -/
  | lab (t : T)

structure LEdge (N S T : Type) where
  src : N
  lbl : LLabel S T
  dst : N

abbrev LGraph (N S T : Type) := Set (LEdge N S T)

/-- Abstract origins: a site's objects not yet seen initialized, or the
objects a labeling point initialized as `t`. -/
inductive LOrigin (N T : Type) where
  | base (z : N)
  | lab (z : N) (t : T)

def LOrigin.root {N T : Type} : LOrigin N T → N
  | .base z => z
  | .lab z _ => z

/-- Two facts may denote one instance: the same labeled origin, or a
plain origin against any label of its site (the wildcard). -/
def meets {N T : Type} : LOrigin N T → LOrigin N T → Prop
  | .base z, .base z' => z = z'
  | .base z, .lab z' _ => z = z'
  | .lab z _, .base z' => z = z'
  | .lab z t, .lab z' t' => z = z' ∧ t = t'

inductive LJudg (N S T : Type) where
  | flow (o : LOrigin N T) (c : Option S) (x : N)
  | mal (x y : N)

inductive LDeriv (M : ShiftMonoid) {N T : Type} (origin : N → Prop)
    (G : LGraph N M.S T) : LJudg N M.S T → Prop where
  | flow_refl (z : N) (hz : origin z) :
      LDeriv M origin G (.flow (.base z) (some M.zero) z)
  | flow_a {o : LOrigin N T} {c : Shift M} {x y : N} :
      LDeriv M origin G (.flow o c x) →
      ({ src := x, lbl := .a, dst := y } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o c y)
  | flow_f {o : LOrigin N T} {c : Shift M} {x y : N} {r : M.S} :
      LDeriv M origin G (.flow o c x) →
      ({ src := x, lbl := .f r, dst := y } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o (shiftComp M c (some r)) y)
  | flow_fx {o : LOrigin N T} {c : Shift M} {x y : N} :
      LDeriv M origin G (.flow o c x) →
      ({ src := x, lbl := .fx, dst := y } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o none y)
  /-- the labeling point mints the label of a plain origin -/
  | flow_lab {z : N} {c : Shift M} {x y : N} {t : T} :
      LDeriv M origin G (.flow (.base z) c x) →
      ({ src := x, lbl := .lab t, dst := y } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow (.lab z t) c y)
  /-- an already-labeled fact passes a labeling point unchanged -/
  | flow_lab_keep {z : N} {c : Shift M} {x y : N} {t t' : T} :
      LDeriv M origin G (.flow (.lab z t') c x) →
      ({ src := x, lbl := .lab t, dst := y } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow (.lab z t') c y)
  | flow_m {o : LOrigin N T} {c : Shift M} {x y : N} :
      LDeriv M origin G (.flow o c x) →
      LDeriv M origin G (.mal x y) →
      LDeriv M origin G (.flow o c y)
  | mal_join {p q cx cy : N} {o o' : LOrigin N T} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : LEdge N M.S T) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o c p) →
      LDeriv M origin G (.flow o' c q) →
      meets o o' →
      LDeriv M origin G (.mal cx cy)
  | mal_joinXL {p q cx cy : N} {o o' : LOrigin N T} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : LEdge N M.S T) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o none p) →
      LDeriv M origin G (.flow o' c q) →
      meets o o' →
      LDeriv M origin G (.mal cx cy)
  | mal_joinXR {p q cx cy : N} {o o' : LOrigin N T} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : LEdge N M.S T) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : LEdge N M.S T) ∈ G →
      LDeriv M origin G (.flow o c p) →
      LDeriv M origin G (.flow o' none q) →
      meets o o' →
      LDeriv M origin G (.mal cx cy)

/-! ## The reference: concrete instances -/

inductive RJudg (N S T : Type) where
  /-- the pointer at `x` may hold instance `(z, l)` at offset `s` -/
  | rflow (z : N) (l : Option T) (s : S) (x : N)
  | rmal (x y : N)

inductive RDeriv (M : ShiftMonoid) {N T : Type} (origin : N → Prop)
    (G : LGraph N M.S T) : RJudg N M.S T → Prop where
  /-- a site's allocation yields an instance, whatever it is later
  initialized as -/
  | crefl (z : N) (l : Option T) (hz : origin z) :
      RDeriv M origin G (.rflow z l M.zero z)
  | ca {z x y : N} {l : Option T} {s : M.S} :
      RDeriv M origin G (.rflow z l s x) →
      ({ src := x, lbl := .a, dst := y } : LEdge N M.S T) ∈ G →
      RDeriv M origin G (.rflow z l s y)
  | cf {z x y : N} {l : Option T} {s r : M.S} :
      RDeriv M origin G (.rflow z l s x) →
      ({ src := x, lbl := .f r, dst := y } : LEdge N M.S T) ∈ G →
      RDeriv M origin G (.rflow z l (M.add s r) y)
  | cfx {z x y : N} {l : Option T} {s : M.S} (s' : M.S) :
      RDeriv M origin G (.rflow z l s x) →
      ({ src := x, lbl := .fx, dst := y } : LEdge N M.S T) ∈ G →
      RDeriv M origin G (.rflow z l s' y)
  /-- FAITHFULNESS: only instances initialized as `t` pass `lab t` -/
  | clab {z x y : N} {s : M.S} {t : T} :
      RDeriv M origin G (.rflow z (some t) s x) →
      ({ src := x, lbl := .lab t, dst := y } : LEdge N M.S T) ∈ G →
      RDeriv M origin G (.rflow z (some t) s y)
  /-- two cells alias when their pointers hold one instance at one
  offset -/
  | cmal {p q cx cy z : N} {l : Option T} {s : M.S} :
      ({ src := p, lbl := .d, dst := cx } : LEdge N M.S T) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : LEdge N M.S T) ∈ G →
      RDeriv M origin G (.rflow z l s p) →
      RDeriv M origin G (.rflow z l s q) →
      RDeriv M origin G (.rmal cx cy)
  | cm {z x y : N} {l : Option T} {s : M.S} :
      RDeriv M origin G (.rflow z l s x) →
      RDeriv M origin G (.rmal x y) →
      RDeriv M origin G (.rflow z l s y)

/-- The abstract origins that may stand for instance `(z, l)`: its
site's plain origin, or its own label. -/
def stands {N T : Type} (z : N) (l : Option T) (o : LOrigin N T) : Prop :=
  o = .base z ∨ ∃ t, l = some t ∧ o = .lab z t

theorem meets_of_stands {N T : Type} {z : N} {l : Option T}
    {o o' : LOrigin N T} (h : stands z l o) (h' : stands z l o') :
    meets o o' := by
  rcases h with rfl | ⟨t, hl, rfl⟩ <;> rcases h' with rfl | ⟨t', hl', rfl⟩
  · exact rfl
  · exact rfl
  · exact rfl
  · subst hl
    cases hl'
    exact ⟨rfl, rfl⟩

def LCovered (M : ShiftMonoid) {N T : Type} (origin : N → Prop)
    (G : LGraph N M.S T) : RJudg N M.S T → Prop
  | .rflow z l s x =>
      ∃ o a, stands z l o ∧ covers a s ∧ LDeriv M origin G (.flow o a x)
  | .rmal x y => LDeriv M origin G (.mal x y)

theorem lmal_of_covers (M : ShiftMonoid) {N T : Type} {origin : N → Prop}
    {G : LGraph N M.S T} {p q x y : N} {o o' : LOrigin N T}
    {a0 b0 : Shift M} {s0 : M.S}
    (hp : ({ src := p, lbl := .d, dst := x } : LEdge N M.S T) ∈ G)
    (hq : ({ src := q, lbl := .d, dst := y } : LEdge N M.S T) ∈ G)
    (ha : covers a0 s0) (dp : LDeriv M origin G (.flow o a0 p))
    (hb : covers b0 s0) (dq : LDeriv M origin G (.flow o' b0 q))
    (hm : meets o o') :
    LDeriv M origin G (.mal x y) := by
  rcases ha with ha | ha
  · subst ha; exact .mal_joinXL hp hq dp dq hm
  · rcases hb with hb | hb
    · subst hb; exact .mal_joinXR hp hq dp dq hm
    · subst ha; subst hb; exact .mal_join hp hq dp dq hm

/-- LABELS ARE SOUND: every concrete flow is covered by the labeled
grammar, through the instance's plain origin or its own label, provided
labeling points are faithful (built into `RDeriv.clab`). -/
theorem label_sound (M : ShiftMonoid) {N T : Type} {origin : N → Prop}
    {G : LGraph N M.S T} :
    ∀ {j : RJudg N M.S T}, RDeriv M origin G j → LCovered M origin G j := by
  intro j d
  induction d with
  | crefl z l hz => exact ⟨.base z, _, Or.inl rfl, Or.inr rfl, .flow_refl z hz⟩
  | ca _ hE ih =>
      obtain ⟨o, a, hs, ha, da⟩ := ih
      exact ⟨o, a, hs, ha, .flow_a da hE⟩
  | cf _ hE ih =>
      obtain ⟨o, a, hs, ha, da⟩ := ih
      exact ⟨o, _, hs, covers_comp _ ha, .flow_f da hE⟩
  | cfx s' _ hE ih =>
      obtain ⟨o, a, hs, _, da⟩ := ih
      exact ⟨o, none, hs, Or.inl rfl, .flow_fx da hE⟩
  | clab _ hE ih =>
      obtain ⟨o, a, hs, ha, da⟩ := ih
      rcases hs with rfl | ⟨t', ht, rfl⟩
      · exact ⟨_, a, Or.inr ⟨_, rfl, rfl⟩, ha, .flow_lab da hE⟩
      · exact ⟨_, a, Or.inr ⟨t', ht, rfl⟩, ha, .flow_lab_keep da hE⟩
  | cmal hp hq _ _ ihp ihq =>
      obtain ⟨o, a, hs, ha, dp⟩ := ihp
      obtain ⟨o', b, hs', hb, dq⟩ := ihq
      exact lmal_of_covers M hp hq ha dp hb dq (meets_of_stands hs hs')
  | cm _ _ ihf ihm =>
      obtain ⟨o, a, hs, ha, da⟩ := ihf
      exact ⟨o, a, hs, ha, .flow_m da ihm⟩

/-! ## Labels only remove answers -/

def eraseLabel {S T : Type} : LLabel S T → FLabel S
  | .a => .a
  | .d => .d
  | .f r => .f r
  | .fx => .fx
  | .lab _ => .a

def eraseGraph {N S T : Type} (G : LGraph N S T) : FGraph N S :=
  fun e => ∃ e', e' ∈ G ∧
    ({ src := e'.src, lbl := eraseLabel e'.lbl, dst := e'.dst } : FEdge N S) = e

def eraseJudg {N S T : Type} : LJudg N S T → FJudg N S
  | .flow o c x => .flow o.root c x
  | .mal x y => .mal x y

theorem erase_mem {N S T : Type} {G : LGraph N S T} {e : LEdge N S T}
    (h : e ∈ G) :
    ({ src := e.src, lbl := eraseLabel e.lbl, dst := e.dst } : FEdge N S) ∈
      eraseGraph G := ⟨e, h, rfl⟩

theorem root_of_meets {N T : Type} {o o' : LOrigin N T} (h : meets o o') :
    o.root = o'.root := by
  cases o <;> cases o' <;> simp [meets, LOrigin.root] at h ⊢
  · exact h
  · exact h
  · exact h
  · exact h.1

/-- Every labeled derivation is a derivation of today's grammar on the
erased graph, with each origin replaced by its site. -/
theorem label_removal_only (M : ShiftMonoid) {N T : Type} {origin : N → Prop}
    {G : LGraph N M.S T} :
    ∀ {j : LJudg N M.S T}, LDeriv M origin G j →
      FDeriv M origin (eraseGraph G) (eraseJudg j) := by
  intro j d
  induction d with
  | flow_refl z hz => exact .flow_refl z hz
  | flow_a _ hE ih => exact .flow_a ih (erase_mem hE)
  | flow_f _ hE ih => exact .flow_f ih (erase_mem hE)
  | flow_fx _ hE ih => exact .flow_fx ih (erase_mem hE)
  | flow_lab _ hE ih => exact .flow_a ih (erase_mem hE)
  | flow_lab_keep _ hE ih => exact .flow_a ih (erase_mem hE)
  | flow_m _ _ ih₁ ih₂ => exact .flow_m ih₁ ih₂
  | mal_join hp hq _ _ hm ihp ihq =>
      have h := root_of_meets hm
      simp only [eraseJudg] at ihp ihq
      rw [h] at ihp
      exact .mal_join (erase_mem hp) (erase_mem hq) ihp ihq
  | mal_joinXL hp hq _ _ hm ihp ihq =>
      have h := root_of_meets hm
      simp only [eraseJudg] at ihp ihq
      rw [h] at ihp
      exact .mal_joinXL (erase_mem hp) (erase_mem hq) ihp ihq
  | mal_joinXR hp hq _ _ hm ihp ihq =>
      have h := root_of_meets hm
      simp only [eraseJudg] at ihp ihq
      rw [h] at ihp
      exact .mal_joinXR (erase_mem hp) (erase_mem hq) ihp ihq

end TypeLabels
