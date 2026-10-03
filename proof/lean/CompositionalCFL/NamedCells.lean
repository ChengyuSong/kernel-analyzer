import CompositionalCFL.FlowsTo

/-!
# Named cells: merged classes keep their content filed by name

Plan `docs/plan-named-cells.md` Part B, section 3.3. The solver merges
memory cells into classes (union-find over alias witnesses); the merge
is what makes the solve fit, and it is where finer distinctions are
lost. Named cells keep the merge but file a class's content under the
NAME of the store that put it there, and let a load read through the
tightest name it is entitled to.

Model. Graph edges are those of the flows-to encoding plus explicit
store and load edges:
- `st n`: value -> cell, the store's address expression has name `n`
  (`none` = unnamed: no struct type, e.g. through `void *`);
- `ld k`: cell -> value, the load reads through name `k`.
A `NamePolicy` says which names are CERTIFIED and which names may
denote the same cells by layout (`lalias n k`: content stored under
`n` may be read through `k`: nested structs, unions).
`adm P n k`: a load through `k` reads plane `n` iff `k` is unnamed,
or `k` is uncertified, or `n` is a layout alias of `k`. Only a
certified load filters; an uncertified named load reads every plane,
exactly as today. (Plan 3.2 item 4 had uncertified named loads skip
other names' planes; with type punning that is unsound, and it
contradicts the plan's own `uncertified_read_eq_today`.)

Results:
- `named_sound_fderiv`: every named derivation is a derivation of the
  flows-to grammar on the erased graph (stores and loads become `a`
  edges) for ANY admissibility relation — named planes only remove
  answers (gate G2's one-sided check is the right gate).
- `named_sub` / `nderiv_adm_mono`: a stricter policy derives less.
- `uncertified_read_eq_today`: with no certified name the named
  derivations are exactly the unfiltered ones.
- `named_read_sound`: against the EXACT reference semantics (exact
  byte offsets, a store and a load meet iff their pointers carry the
  same object and offset), the named derivations cover every concrete
  value flow, under ONE hypothesis, `CertConsistent`: a store whose
  cell a certified load reads names an alias of that load's name. That
  hypothesis is what the certificate census (plan 3.4) must discharge
  syntactically: no escaped field address, no bulk copy, no atomic, no
  variable offset, no copy-in from an open name, and the bare-pointer
  rule (stores with no struct name open every name they could cover).
- `read_merge`, `read_noleak`, `merge_keeps_names`
  (= `merge_lossless_named`): planes merge name by name; a certified
  read of a merged class returns exactly the union of the members'
  admissible planes and never content filed under a non-alias name.
- `nbatched_exact` (= `batched_named_eq`): the batched solver's
  exactness (union of per-batch closures against a sound, closed
  witness table = the eager closure) holds unchanged with
  name-indexed planes: names never create cross-origin dependence.
-/

namespace NamedCells

open CompositionalCFL (Set)
open FlowsToCFL

/-! ## Graphs with named stores and loads -/

inductive NLabel (S Nm : Type) where
  | a
  | d
  | f (r : S)
  | fx
  | st (n : Option Nm)
  | ld (k : Option Nm)

structure NEdge (N S Nm : Type) where
  src : N
  lbl : NLabel S Nm
  dst : N

abbrev NGraph (N S Nm : Type) := Set (NEdge N S Nm)

/-- Which names are certified, and which names may denote the same
cells by layout (`lalias n k`: content filed under `n` may be read
through `k`). -/
structure NamePolicy (Nm : Type) where
  cert : Nm → Prop
  lalias : Nm → Nm → Prop

/-- A load through `k` reads plane `n`. -/
def adm {Nm : Type} (P : NamePolicy Nm) (n : Option Nm) : Option Nm → Prop
  | none => True
  | some k => ¬ P.cert k ∨ ∃ n', n = some n' ∧ P.lalias n' k

/-- Today's solver: every load reads every plane. -/
def admAll {Nm : Type} (_ _ : Option Nm) : Prop := True

/-- Judgments: a value flow, a value filed in a cell under a store
name, a cell alias. -/
inductive NJudg (N S Nm : Type) where
  | flow (z : N) (c : Option S) (x : N)
  | cell (z : N) (c : Option S) (x : N) (n : Option Nm)
  | mal (x y : N)

/-- Declarative named derivations, rooted at origins. `adm` decides
which planes a load reads. Cells merge (`cell_m`) keeping the store
name: that is the whole content of "merging keeps names". A cell's
content used as a pointer value (`cell_val`) is an unnamed read. -/
inductive NDeriv (M : ShiftMonoid) {N Nm : Type} (origin : N → Prop)
    (adm : Option Nm → Option Nm → Prop) (G : NGraph N M.S Nm) :
    NJudg N M.S Nm → Prop where
  | flow_refl (z : N) (hz : origin z) :
      NDeriv M origin adm G (.flow z (some M.zero) z)
  | flow_a {z : N} {c : Shift M} {x y : N} :
      NDeriv M origin adm G (.flow z c x) →
      ({ src := x, lbl := .a, dst := y } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z c y)
  | flow_f {z : N} {c : Shift M} {x y : N} {r : M.S} :
      NDeriv M origin adm G (.flow z c x) →
      ({ src := x, lbl := .f r, dst := y } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z (shiftComp M c (some r)) y)
  | flow_fx {z : N} {c : Shift M} {x y : N} :
      NDeriv M origin adm G (.flow z c x) →
      ({ src := x, lbl := .fx, dst := y } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z none y)
  | store {z : N} {c : Shift M} {v x : N} {n : Option Nm} :
      NDeriv M origin adm G (.flow z c v) →
      ({ src := v, lbl := .st n, dst := x } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.cell z c x n)
  | cell_m {z : N} {c : Shift M} {x y : N} {n : Option Nm} :
      NDeriv M origin adm G (.cell z c x n) →
      NDeriv M origin adm G (.mal x y) →
      NDeriv M origin adm G (.cell z c y n)
  | load {z : N} {c : Shift M} {y r : N} {n k : Option Nm} :
      NDeriv M origin adm G (.cell z c y n) →
      ({ src := y, lbl := .ld k, dst := r } : NEdge N M.S Nm) ∈ G →
      adm n k →
      NDeriv M origin adm G (.flow z c r)
  | cell_val {z : N} {c : Shift M} {y : N} {n : Option Nm} :
      NDeriv M origin adm G (.cell z c y n) →
      NDeriv M origin adm G (.flow z c y)
  | mal_join {p q cx cy z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z c p) →
      NDeriv M origin adm G (.flow z c q) →
      NDeriv M origin adm G (.mal cx cy)
  | mal_joinXL {p q cx cy z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z none p) →
      NDeriv M origin adm G (.flow z c q) →
      NDeriv M origin adm G (.mal cx cy)
  | mal_joinXR {p q cx cy z : N} {c : Shift M} :
      ({ src := p, lbl := .d, dst := cx } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := cy } : NEdge N M.S Nm) ∈ G →
      NDeriv M origin adm G (.flow z c p) →
      NDeriv M origin adm G (.flow z none q) →
      NDeriv M origin adm G (.mal cx cy)

/-! ## Named derivations only remove answers -/

/-- A stricter admissibility derives less. -/
theorem nderiv_adm_mono (M : ShiftMonoid) {N Nm : Type} {origin : N → Prop}
    {a₁ a₂ : Option Nm → Option Nm → Prop} {G : NGraph N M.S Nm}
    (h : ∀ n k, a₁ n k → a₂ n k) :
    ∀ {j : NJudg N M.S Nm}, NDeriv M origin a₁ G j → NDeriv M origin a₂ G j := by
  intro j d
  induction d with
  | flow_refl z hz => exact .flow_refl z hz
  | flow_a _ hE ih => exact .flow_a ih hE
  | flow_f _ hE ih => exact .flow_f ih hE
  | flow_fx _ hE ih => exact .flow_fx ih hE
  | store _ hE ih => exact .store ih hE
  | cell_m _ _ ih₁ ih₂ => exact .cell_m ih₁ ih₂
  | load _ hE ha ih => exact .load ih hE (h _ _ ha)
  | cell_val _ ih => exact .cell_val ih
  | mal_join hp hq _ _ ihp ihq => exact .mal_join hp hq ihp ihq
  | mal_joinXL hp hq _ _ ihp ihq => exact .mal_joinXL hp hq ihp ihq
  | mal_joinXR hp hq _ _ ihp ihq => exact .mal_joinXR hp hq ihp ihq

/-- Named reads derive a subset of the unfiltered reads. -/
theorem named_sub (M : ShiftMonoid) {N Nm : Type} {origin : N → Prop}
    (P : NamePolicy Nm) {G : NGraph N M.S Nm} {j : NJudg N M.S Nm}
    (d : NDeriv M origin (adm P) G j) : NDeriv M origin admAll G j :=
  nderiv_adm_mono M (fun _ _ _ => trivial) d

/-- With no certified name, a named load reads every plane: the named
derivations are exactly today's. -/
theorem uncertified_read_eq_today (M : ShiftMonoid) {N Nm : Type}
    {origin : N → Prop} (P : NamePolicy Nm) {G : NGraph N M.S Nm}
    (hnone : ∀ k, ¬ P.cert k) {j : NJudg N M.S Nm} :
    NDeriv M origin (adm P) G j ↔ NDeriv M origin admAll G j := by
  constructor
  · exact named_sub M P
  · intro d
    refine nderiv_adm_mono M ?_ d
    intro n k _
    cases k with
    | none => trivial
    | some k => exact Or.inl (hnone k)

/-- Erase names: stores and loads become `a` edges. -/
def eraseLabel {S Nm : Type} : NLabel S Nm → FLabel S
  | .a => .a
  | .d => .d
  | .f r => .f r
  | .fx => .fx
  | .st _ => .a
  | .ld _ => .a

def eraseEdge {N S Nm : Type} (e : NEdge N S Nm) : FEdge N S :=
  { src := e.src, lbl := eraseLabel e.lbl, dst := e.dst }

def eraseGraph {N S Nm : Type} (G : NGraph N S Nm) : FGraph N S :=
  fun e => ∃ e', e' ∈ G ∧ eraseEdge e' = e

/-- A value filed in a cell is a flow to the cell in the grammar. -/
def eraseJudg {N S Nm : Type} : NJudg N S Nm → FJudg N S
  | .flow z c x => .flow z c x
  | .cell z c x _ => .flow z c x
  | .mal x y => .mal x y

theorem erase_mem {N S Nm : Type} {G : NGraph N S Nm} {e : NEdge N S Nm}
    (h : e ∈ G) : eraseEdge e ∈ eraseGraph G := ⟨e, h, rfl⟩

/-- Every named derivation, for ANY admissibility, is a derivation of
the flows-to grammar on the erased graph: named planes are
removal-only with respect to the current solver's specification. -/
theorem named_sound_fderiv (M : ShiftMonoid) {N Nm : Type}
    {origin : N → Prop} {a : Option Nm → Option Nm → Prop}
    {G : NGraph N M.S Nm} :
    ∀ {j : NJudg N M.S Nm}, NDeriv M origin a G j →
      FDeriv M origin (eraseGraph G) (eraseJudg j) := by
  intro j d
  induction d with
  | flow_refl z hz => exact .flow_refl z hz
  | flow_a _ hE ih => exact .flow_a ih (erase_mem hE)
  | flow_f _ hE ih => exact .flow_f ih (erase_mem hE)
  | flow_fx _ hE ih => exact .flow_fx ih (erase_mem hE)
  | store _ hE ih => exact .flow_a ih (erase_mem hE)
  | cell_m _ _ ih₁ ih₂ => exact .flow_m ih₁ ih₂
  | load _ hE _ ih => exact .flow_a ih (erase_mem hE)
  | cell_val _ ih => exact ih
  | mal_join hp hq _ _ ihp ihq =>
      exact .mal_join (erase_mem hp) (erase_mem hq) ihp ihq
  | mal_joinXL hp hq _ _ ihp ihq =>
      exact .mal_joinXL (erase_mem hp) (erase_mem hq) ihp ihq
  | mal_joinXR hp hq _ _ ihp ihq =>
      exact .mal_joinXR (erase_mem hp) (erase_mem hq) ihp ihq

/-! ## Soundness of named reads against the exact reference semantics

The reference semantics is the flows-to grammar with EXACT offsets and
no unknown shift: a store through `p` and a load through `q` touch the
same cell iff `p` and `q` carry the same object `z0` at the same offset
`s0`. It is the most precise flow-insensitive, context-insensitive
semantics over this graph; its own soundness for machine executions
is the standard inclusion-based argument and is assumed, as today.
`fx` steps move to an arbitrary concrete offset. -/

inductive CJudg (N S Nm : Type) where
  | cflow (z : N) (s : S) (x : N)
  /-- value `(z, s)` stored into the concrete cell `(z0, s0)` by a store
  named `n` -/
  | ccell (z : N) (s : S) (z0 : N) (s0 : S) (n : Option Nm)

inductive CDeriv (M : ShiftMonoid) {N Nm : Type} (origin : N → Prop)
    (G : NGraph N M.S Nm) : CJudg N M.S Nm → Prop where
  | crefl (z : N) (hz : origin z) : CDeriv M origin G (.cflow z M.zero z)
  | ca {z x y : N} {s : M.S} :
      CDeriv M origin G (.cflow z s x) →
      ({ src := x, lbl := .a, dst := y } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z s y)
  | cf {z x y : N} {s r : M.S} :
      CDeriv M origin G (.cflow z s x) →
      ({ src := x, lbl := .f r, dst := y } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z (M.add s r) y)
  | cfx {z x y : N} {s : M.S} (s' : M.S) :
      CDeriv M origin G (.cflow z s x) →
      ({ src := x, lbl := .fx, dst := y } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z s' y)
  | cstore {z v x p z0 : N} {s s0 : M.S} {n : Option Nm} :
      CDeriv M origin G (.cflow z s v) →
      ({ src := v, lbl := .st n, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z0 s0 p) →
      CDeriv M origin G (.ccell z s z0 s0 n)
  | cload {z q y r z0 : N} {s s0 : M.S} {n k : Option Nm} :
      CDeriv M origin G (.ccell z s z0 s0 n) →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z0 s0 q) →
      ({ src := y, lbl := .ld k, dst := r } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z s r)
  | cval {z q y z0 : N} {s s0 : M.S} {n : Option Nm} :
      CDeriv M origin G (.ccell z s z0 s0 n) →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      CDeriv M origin G (.cflow z0 s0 q) →
      CDeriv M origin G (.cflow z s y)

/-- The certificate's meaning: whenever a load through a CERTIFIED name
`k` reads a concrete cell, every store that wrote that cell named a
layout alias of `k`. The census discharges it syntactically (plan 3.4);
here it is the one hypothesis named reads rest on. -/
def CertConsistent (M : ShiftMonoid) {N Nm : Type} (origin : N → Prop)
    (P : NamePolicy Nm) (G : NGraph N M.S Nm) : Prop :=
  ∀ {z q y r z0 : N} {s s0 : M.S} {n : Option Nm} {k : Nm},
    CDeriv M origin G (.ccell z s z0 s0 n) →
    ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
    CDeriv M origin G (.cflow z0 s0 q) →
    ({ src := y, lbl := .ld (some k), dst := r } : NEdge N M.S Nm) ∈ G →
    P.cert k → ∃ n', n = some n' ∧ P.lalias n' k

/-- An abstract shift covers a concrete offset: equal, or unknown. -/
def covers {M : ShiftMonoid} (a : Shift M) (s : M.S) : Prop :=
  a = none ∨ a = some s

theorem covers_comp {M : ShiftMonoid} {a : Shift M} {s : M.S} (r : M.S)
    (h : covers a s) : covers (shiftComp M a (some r)) (M.add s r) := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · subst h; exact Or.inr rfl

/-- What a concrete judgment guarantees of the named derivations. -/
def Covered (M : ShiftMonoid) {N Nm : Type} (origin : N → Prop)
    (P : NamePolicy Nm) (G : NGraph N M.S Nm) : CJudg N M.S Nm → Prop
  | .cflow z s x =>
      ∃ a, covers a s ∧ NDeriv M origin (adm P) G (.flow z a x)
  | .ccell z s z0 s0 n =>
      ∃ x p a a0,
        ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G ∧
        covers a s ∧ NDeriv M origin (adm P) G (.cell z a x n) ∧
        covers a0 s0 ∧ NDeriv M origin (adm P) G (.flow z0 a0 p)

/-- Two pointers whose abstract shifts cover the same concrete offset
of the same object alias their cells. -/
theorem mal_of_covers (M : ShiftMonoid) {N Nm : Type} {origin : N → Prop}
    {P : NamePolicy Nm} {G : NGraph N M.S Nm} {p q x y z0 : N}
    {a0 b0 : Shift M} {s0 : M.S}
    (hp : ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G)
    (hq : ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G)
    (ha : covers a0 s0) (dp : NDeriv M origin (adm P) G (.flow z0 a0 p))
    (hb : covers b0 s0) (dq : NDeriv M origin (adm P) G (.flow z0 b0 q)) :
    NDeriv M origin (adm P) G (.mal x y) := by
  rcases ha with ha | ha
  · subst ha; exact .mal_joinXL hp hq dp dq
  · rcases hb with hb | hb
    · subst hb; exact .mal_joinXR hp hq dp dq
    · subst ha; subst hb; exact .mal_join hp hq dp dq

/-- NAMED READS ARE SOUND: every concrete value flow is covered by a
named derivation, provided the certificate is consistent. -/
theorem named_read_sound (M : ShiftMonoid) {N Nm : Type}
    {origin : N → Prop} (P : NamePolicy Nm) {G : NGraph N M.S Nm}
    (hcert : CertConsistent M origin P G) :
    ∀ {j : CJudg N M.S Nm}, CDeriv M origin G j → Covered M origin P G j := by
  intro j d
  induction d with
  | crefl z hz => exact ⟨_, Or.inr rfl, .flow_refl z hz⟩
  | ca _ hE ih =>
      obtain ⟨a, ha, da⟩ := ih
      exact ⟨a, ha, .flow_a da hE⟩
  | cf _ hE ih =>
      obtain ⟨a, ha, da⟩ := ih
      exact ⟨_, covers_comp _ ha, .flow_f da hE⟩
  | cfx s' _ hE ih =>
      obtain ⟨a, _, da⟩ := ih
      exact ⟨none, Or.inl rfl, .flow_fx da hE⟩
  | cstore _ hE hD _ ihv ihp =>
      obtain ⟨a, ha, da⟩ := ihv
      obtain ⟨a0, ha0, dp⟩ := ihp
      exact ⟨_, _, a, a0, hD, ha, .store da hE, ha0, dp⟩
  | cload dc hq dq hL ihc ihq =>
      obtain ⟨x, p, a, a0, hp, ha, dcell, ha0, dp⟩ := ihc
      obtain ⟨b0, hb0, dq'⟩ := ihq
      have hmal := mal_of_covers M hp hq ha0 dp hb0 dq'
      refine ⟨a, ha, .load (.cell_m dcell hmal) hL ?_⟩
      rename_i k
      cases k with
      | none => trivial
      | some k =>
          by_cases hc : P.cert k
          · exact Or.inr (hcert dc hq dq hL hc)
          · exact Or.inl hc
  | cval _ hq _ ihc ihq =>
      obtain ⟨x, p, a, a0, hp, ha, dcell, ha0, dp⟩ := ihc
      obtain ⟨b0, hb0, dq'⟩ := ihq
      exact ⟨a, ha, .cell_val (.cell_m dcell (mal_of_covers M hp hq ha0 dp hb0 dq'))⟩

/-! ## Merging keeps names (`merge_lossless_named`)

The solver's class planes, indexed by name. A merge ORs the planes
name by name; a read unions the admissible planes. -/

/-- Planes of a class: per store name, a set of facts. -/
abbrev Planes (Nm F : Type) := Option Nm → Set F

def mergePlanes {Nm F : Type} (A B : Planes Nm F) : Planes Nm F :=
  fun n f => A n f ∨ B n f

def readPlanes {Nm F : Type} (P : NamePolicy Nm) (pl : Planes Nm F)
    (k : Option Nm) : Set F :=
  fun f => ∃ n, adm P n k ∧ pl n f

/-- Merging loses nothing filed under any name. -/
theorem merge_keeps_names {Nm F : Type} (A B : Planes Nm F) (n : Option Nm)
    (f : F) (h : A n f) : mergePlanes A B n f := Or.inl h

/-- A read of a merged class is the union of the members' reads. -/
theorem read_merge {Nm F : Type} (P : NamePolicy Nm) (A B : Planes Nm F)
    (k : Option Nm) (f : F) :
    readPlanes P (mergePlanes A B) k f ↔ readPlanes P A k f ∨ readPlanes P B k f := by
  constructor
  · rintro ⟨n, ha, hA | hB⟩
    · exact Or.inl ⟨n, ha, hA⟩
    · exact Or.inr ⟨n, ha, hB⟩
  · rintro (⟨n, ha, hA⟩ | ⟨n, ha, hB⟩)
    · exact ⟨n, ha, Or.inl hA⟩
    · exact ⟨n, ha, Or.inr hB⟩

/-- A certified read never returns content filed under a name that is
not a layout alias (including the unnamed plane), however the classes
merged. -/
theorem read_noleak {Nm F : Type} (P : NamePolicy Nm) (pl : Planes Nm F)
    {k : Nm} (hk : P.cert k) {f : F} (h : readPlanes P pl (some k) f) :
    ∃ n', pl (some n') f ∧ P.lalias n' k := by
  obtain ⟨n, ha, hpl⟩ := h
  rcases ha with ha | ⟨n', hn, hl⟩
  · exact absurd hk ha
  · subst hn; exact ⟨n', hpl, hl⟩

/-! ## Batched solving with name-indexed planes (`batched_named_eq`)

`NSDeriv` is the named analogue of `FlowsToCFL.SDeriv` (one drain from
minted roots, joins flattened), `NWDeriv` the analogue of `WDeriv` (one
batch's drain with joins consuming witness facts from a table). The
witness facts are FLOW facts at the cells' parent pointers; planes
enter only through loads and cell values, which stay within the
origin's own derivation. So the batched argument goes through
unchanged. -/

inductive SJ (N S Nm : Type) where
  | flow (m : N) (c : Option S) (x : N)
  | cell (m : N) (c : Option S) (x : N) (n : Option Nm)

inductive NSDeriv (M : ShiftMonoid) {N Nm : Type} (P : NamePolicy Nm)
    (G : NGraph N M.S Nm) (minted : N → Prop) : SJ N M.S Nm → Prop where
  | seed (m : N) (hm : minted m) : NSDeriv M P G minted (.flow m (some M.zero) m)
  | step_a {m x y : N} {c : Shift M} :
      NSDeriv M P G minted (.flow m c x) →
      ({ src := x, lbl := .a, dst := y } : NEdge N M.S Nm) ∈ G →
      NSDeriv M P G minted (.flow m c y)
  | step_f {m x y : N} {c : Shift M} {r : M.S} :
      NSDeriv M P G minted (.flow m c x) →
      ({ src := x, lbl := .f r, dst := y } : NEdge N M.S Nm) ∈ G →
      NSDeriv M P G minted (.flow m (shiftComp M c (some r)) y)
  | step_fx {m x y : N} {c : Shift M} :
      NSDeriv M P G minted (.flow m c x) →
      ({ src := x, lbl := .fx, dst := y } : NEdge N M.S Nm) ∈ G →
      NSDeriv M P G minted (.flow m none y)
  | store {m v x : N} {c : Shift M} {n : Option Nm} :
      NSDeriv M P G minted (.flow m c v) →
      ({ src := v, lbl := .st n, dst := x } : NEdge N M.S Nm) ∈ G →
      NSDeriv M P G minted (.cell m c x n)
  | load {m y r : N} {c : Shift M} {n k : Option Nm} :
      NSDeriv M P G minted (.cell m c y n) →
      ({ src := y, lbl := .ld k, dst := r } : NEdge N M.S Nm) ∈ G →
      adm P n k →
      NSDeriv M P G minted (.flow m c r)
  | cval {m y : N} {c : Shift M} {n : Option Nm} :
      NSDeriv M P G minted (.cell m c y n) →
      NSDeriv M P G minted (.flow m c y)
  | join_e {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      minted w →
      NSDeriv M P G minted (.flow w cw p) →
      NSDeriv M P G minted (.flow w cw q) →
      NSDeriv M P G minted (.cell m c x n) →
      NSDeriv M P G minted (.cell m c y n)
  | join_xl {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      minted w →
      NSDeriv M P G minted (.flow w none p) →
      NSDeriv M P G minted (.flow w cw q) →
      NSDeriv M P G minted (.cell m c x n) →
      NSDeriv M P G minted (.cell m c y n)
  | join_xr {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      minted w →
      NSDeriv M P G minted (.flow w cw p) →
      NSDeriv M P G minted (.flow w none q) →
      NSDeriv M P G minted (.cell m c x n) →
      NSDeriv M P G minted (.cell m c y n)

inductive NWDeriv (M : ShiftMonoid) {N Nm : Type} (P : NamePolicy Nm)
    (G : NGraph N M.S Nm) (minted : N → Prop) (W : N → Shift M → N → Prop) :
    SJ N M.S Nm → Prop where
  | seed (m : N) (hm : minted m) : NWDeriv M P G minted W (.flow m (some M.zero) m)
  | step_a {m x y : N} {c : Shift M} :
      NWDeriv M P G minted W (.flow m c x) →
      ({ src := x, lbl := .a, dst := y } : NEdge N M.S Nm) ∈ G →
      NWDeriv M P G minted W (.flow m c y)
  | step_f {m x y : N} {c : Shift M} {r : M.S} :
      NWDeriv M P G minted W (.flow m c x) →
      ({ src := x, lbl := .f r, dst := y } : NEdge N M.S Nm) ∈ G →
      NWDeriv M P G minted W (.flow m (shiftComp M c (some r)) y)
  | step_fx {m x y : N} {c : Shift M} :
      NWDeriv M P G minted W (.flow m c x) →
      ({ src := x, lbl := .fx, dst := y } : NEdge N M.S Nm) ∈ G →
      NWDeriv M P G minted W (.flow m none y)
  | store {m v x : N} {c : Shift M} {n : Option Nm} :
      NWDeriv M P G minted W (.flow m c v) →
      ({ src := v, lbl := .st n, dst := x } : NEdge N M.S Nm) ∈ G →
      NWDeriv M P G minted W (.cell m c x n)
  | load {m y r : N} {c : Shift M} {n k : Option Nm} :
      NWDeriv M P G minted W (.cell m c y n) →
      ({ src := y, lbl := .ld k, dst := r } : NEdge N M.S Nm) ∈ G →
      adm P n k →
      NWDeriv M P G minted W (.flow m c r)
  | cval {m y : N} {c : Shift M} {n : Option Nm} :
      NWDeriv M P G minted W (.cell m c y n) →
      NWDeriv M P G minted W (.flow m c y)
  | join_e {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      W w cw p → W w cw q →
      NWDeriv M P G minted W (.cell m c x n) →
      NWDeriv M P G minted W (.cell m c y n)
  | join_xl {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      W w none p → W w cw q →
      NWDeriv M P G minted W (.cell m c x n) →
      NWDeriv M P G minted W (.cell m c y n)
  | join_xr {m x y p q w : N} {c cw : Shift M} {n : Option Nm} :
      ({ src := p, lbl := .d, dst := x } : NEdge N M.S Nm) ∈ G →
      ({ src := q, lbl := .d, dst := y } : NEdge N M.S Nm) ∈ G →
      W w cw p → W w none q →
      NWDeriv M P G minted W (.cell m c x n) →
      NWDeriv M P G minted W (.cell m c y n)

/-- The origin of a judgment. -/
def SJ.origin {N S Nm : Type} : SJ N S Nm → N
  | .flow m _ _ => m
  | .cell m _ _ _ => m

/-- Every fact of a drain carries a minted origin. -/
theorem nsderiv_origin_minted (M : ShiftMonoid) {N Nm : Type}
    {P : NamePolicy Nm} {G : NGraph N M.S Nm} {minted : N → Prop} :
    ∀ {j : SJ N M.S Nm}, NSDeriv M P G minted j → minted j.origin := by
  intro j d
  induction d with
  | seed m hm => exact hm
  | step_a _ _ ih => exact ih
  | step_f _ _ ih => exact ih
  | step_fx _ _ ih => exact ih
  | store _ _ ih => exact ih
  | load _ _ _ ih => exact ih
  | cval _ ih => exact ih
  | join_e _ _ _ _ _ _ _ _ ihx => exact ihx
  | join_xl _ _ _ _ _ _ _ _ ihx => exact ihx
  | join_xr _ _ _ _ _ _ _ _ ihx => exact ihx

/-- A batch drained against a sound table stays inside the eager closure. -/
theorem nwderiv_sound (M : ShiftMonoid) {N Nm : Type} {P : NamePolicy Nm}
    {G : NGraph N M.S Nm} {mb m₂ : N → Prop} {W : N → Shift M → N → Prop}
    (hsub : ∀ n, mb n → m₂ n)
    (hW : ∀ w cw x, W w cw x → NSDeriv M P G m₂ (.flow w cw x)) :
    ∀ {j : SJ N M.S Nm}, NWDeriv M P G mb W j → NSDeriv M P G m₂ j := by
  intro j d
  induction d with
  | seed m hm => exact .seed m (hsub _ hm)
  | step_a _ hE ih => exact .step_a ih hE
  | step_f _ hE ih => exact .step_f ih hE
  | step_fx _ hE ih => exact .step_fx ih hE
  | store _ hE ih => exact .store ih hE
  | load _ hE ha ih => exact .load ih hE ha
  | cval _ ih => exact .cval ih
  | join_e hp hq hWp hWq _ ihx =>
      exact .join_e hp hq (nsderiv_origin_minted M (hW _ _ _ hWp))
        (hW _ _ _ hWp) (hW _ _ _ hWq) ihx
  | join_xl hp hq hWp hWq _ ihx =>
      exact .join_xl hp hq (nsderiv_origin_minted M (hW _ _ _ hWp))
        (hW _ _ _ hWp) (hW _ _ _ hWq) ihx
  | join_xr hp hq hWp hWq _ ihx =>
      exact .join_xr hp hq (nsderiv_origin_minted M (hW _ _ _ hWp))
        (hW _ _ _ hWp) (hW _ _ _ hWq) ihx

/-- At a closed table every eager fact appears in its own origin's batch. -/
theorem nwderiv_complete (M : ShiftMonoid) {N Nm : Type} {P : NamePolicy Nm}
    {G : NGraph N M.S Nm} {m₂ : N → Prop} {W : N → Shift M → N → Prop}
    {ι : Type} {b : ι → N → Prop}
    (hcover : ∀ n, m₂ n → ∃ i, b i n)
    (hclosed : ∀ (i : ι) (m : N) (c : Shift M) (x : N),
        NWDeriv M P G (b i) W (.flow m c x) → W m c x) :
    ∀ {j : SJ N M.S Nm}, NSDeriv M P G m₂ j →
      ∃ i, b i j.origin ∧ NWDeriv M P G (b i) W j := by
  intro j d
  induction d with
  | seed n hn =>
      obtain ⟨i, hi⟩ := hcover n hn
      exact ⟨i, hi, .seed _ hi⟩
  | step_a _ hE ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .step_a d hE⟩
  | step_f _ hE ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .step_f d hE⟩
  | step_fx _ hE ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .step_fx d hE⟩
  | store _ hE ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .store d hE⟩
  | load _ hE ha ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .load d hE ha⟩
  | cval _ ih =>
      obtain ⟨i, hi, d⟩ := ih
      exact ⟨i, hi, .cval d⟩
  | join_e hp hq _ _ _ _ ihp ihq ihx =>
      obtain ⟨iw, _, dp⟩ := ihp
      obtain ⟨iw', _, dq⟩ := ihq
      obtain ⟨i, hi, dx⟩ := ihx
      exact ⟨i, hi, .join_e hp hq (hclosed iw _ _ _ dp) (hclosed iw' _ _ _ dq) dx⟩
  | join_xl hp hq _ _ _ _ ihp ihq ihx =>
      obtain ⟨iw, _, dp⟩ := ihp
      obtain ⟨iw', _, dq⟩ := ihq
      obtain ⟨i, hi, dx⟩ := ihx
      exact ⟨i, hi, .join_xl hp hq (hclosed iw _ _ _ dp) (hclosed iw' _ _ _ dq) dx⟩
  | join_xr hp hq _ _ _ _ ihp ihq ihx =>
      obtain ⟨iw, _, dp⟩ := ihp
      obtain ⟨iw', _, dq⟩ := ihq
      obtain ⟨i, hi, dx⟩ := ihx
      exact ⟨i, hi, .join_xr hp hq (hclosed iw _ _ _ dp) (hclosed iw' _ _ _ dq) dx⟩

/-- BATCHED EXACTNESS WITH NAMED PLANES: with a sound, closed witness
table, the union of per-batch named closures is exactly the eager named
closure (`FlowsToCFL.batched_exact` with name-indexed cells). -/
theorem nbatched_exact (M : ShiftMonoid) {N Nm : Type} {P : NamePolicy Nm}
    {G : NGraph N M.S Nm} {m₂ : N → Prop} {W : N → Shift M → N → Prop}
    {ι : Type} {b : ι → N → Prop}
    (hsub : ∀ i n, b i n → m₂ n)
    (hcover : ∀ n, m₂ n → ∃ i, b i n)
    (hsound : ∀ w cw x, W w cw x → NSDeriv M P G m₂ (.flow w cw x))
    (hclosed : ∀ (i : ι) (m : N) (c : Shift M) (x : N),
        NWDeriv M P G (b i) W (.flow m c x) → W m c x)
    {j : SJ N M.S Nm} :
    NSDeriv M P G m₂ j ↔ ∃ i, b i j.origin ∧ NWDeriv M P G (b i) W j := by
  constructor
  · exact nwderiv_complete M hcover hclosed
  · rintro ⟨i, _, d⟩
    exact nwderiv_sound M (hsub i) hsound d

end NamedCells
