import CompositionalCFL.Core

/-!
# Keys: soundness of the call graph for executions that obey three rules

Plan `docs/plan-named-cells.md` 3.10 and 3.11. This file states the
analysis against a CONCRETE semantics, not against a declarative grammar.

## The principle

The analysis does not assume C is well behaved. It states rules, builds the
call graph for every execution that obeys them, and reports every place a
program breaks them:
- (a) no pointer is created from external data: a pointer value exists only
  by taking an address, by an allocator, or from the environment's own
  objects (`NoForge`);
- (b) an object is accessed only as what it is: every load and store touches
  a location inside the key the analysis assigned to that access
  (`AccessAgree`; for a named access this is `PunFree`);
- (c) a certified field receives no untyped write: the same `AccessAgree`,
  for an untyped write whose key excludes the certified fields.
The key transformers carry the rest: field steps cover the concrete address
arithmetic (`FieldCover`) and instance refinements (labels, tags, holder
clones) are faithful (`Faithful`).

## The model

- Concrete: values are pointers to locations, functions, or data. Memory
  starts as data, except that environment objects may point to other
  environment objects (`EnvInit`); the environment never holds code. A
  program is a SET of statements, any of which may run at any time (flow
  insensitivity); `Reach` is every state some sequence of steps produces.
  A load or store through a non-pointer does not step (undefined behavior).
- Keys: every operation that says something about memory assigns a key when
  the graph is built (an allocation a site key, a GEP a position, a label or
  tag an instance key). A key `k` denotes the locations `γ k`. A cell is a
  key. A load reads the cells that MEET its key; `meets` must hold whenever
  two keys share a location (`MeetSound`), and may hold more often.
- Abstract: any `Solution` closed under the rules, not only the least one.
  There are no identity roots: a read of a cell nothing wrote yields nothing.

## Results

- `keys_sound`: every reachable state is covered by every closed solution.
- `icall_sound`: every function an indirect call actually calls is in its
  answer.
- `coarsen_sound`: replacing `meets` by any larger relation (union-find
  clusters make it transitive) keeps soundness; merging is a sound
  coarsening with a precision cost, never a soundness one.
- `ProductKey`: keys as (site, position, instance) with componentwise meet;
  `product_meetSound`, `product_meetKSound`, `product_fieldCover` and
  `product_faithful` reduce each obligation to its own dimension.

Correlated reads (`dcall`, the (callback, data) idiom `p->fn(p->data)`)
bind the callee and its argument through the SAME key of `p`. They are
therefore exactly as precise as the instance dimension of that key: all
timers from one unlabeled site still cross-multiply within the site.
-/

namespace Keys

/-! ## Statements and concrete semantics -/

variable {V L F A T K : Type}

/-- Program statements. `A`: field steps; `T`: instance refinements
(labels, tags); `K`: keys. -/
inductive Stmt (V A T K F : Type) where
  | alloc (x : V) (k : K)            -- x := a fresh object; its site key
  | fnaddr (x : V) (f : F)           -- x := &f
  | copy (x y : V)                   -- x := y
  | field (x y : V) (a : A)          -- x := y + step a (GEP)
  | lab (x y : V) (t : T)            -- x := y; the object is initialized as t
  | i2p (x y : V)                    -- x := (pointer) y
  | load (x y : V) (ka : K)          -- x := *y, access key ka
  | store (x : V) (ka : K) (y : V)   -- *x := y, access key ka
  | icall (x : V) (i : Nat) (y : V)  -- call x, argument i := y
  | icallRet (r x : V)               -- r := call x (return value)
  | dcall (x : V) (afn adata : A) (i : Nat)
      -- call x->fn with argument i := x->data (correlated read)

inductive Val (L F : Type) where
  | ptr (l : L)
  | fn (f : F)
  | data

structure State (V L F : Type) where
  var : V → Val L F
  mem : L → Val L F

/-- The concrete meaning of the program's vocabulary. -/
structure Concrete (V L F A : Type) where
  /-- `isAlloc k l`: `l` is the start of an object an allocation with site
  key `k` may return. -/
  isAlloc : K → L → Prop
  /-- Concrete address arithmetic of a field step. -/
  stepC : A → L → L
  formal : F → Nat → V
  ret : F → V
  mem0 : L → Val L F

def upd {α β : Type} [DecidableEq α] (g : α → β) (a : α) (b : β) : α → β :=
  fun a' => if a' = a then b else g a'

section Semantics

variable [DecidableEq V] [DecidableEq L]
variable (C : Concrete (K := K) V L F A) (P : Stmt V A T K F → Prop)

/-- One step: any statement of the program, at any time. -/
inductive Step : State V L F → State V L F → Prop where
  | alloc {σ : State V L F} {x : V} {k : K} {l : L} :
      P (.alloc x k) → C.isAlloc k l →
      Step σ { σ with var := upd σ.var x (.ptr l) }
  | fnaddr {σ : State V L F} {x : V} {f : F} :
      P (.fnaddr x f) → Step σ { σ with var := upd σ.var x (.fn f) }
  | copy {σ : State V L F} {x y : V} :
      P (.copy x y) → Step σ { σ with var := upd σ.var x (σ.var y) }
  | field {σ : State V L F} {x y : V} {a : A} {l : L} :
      P (.field x y a) → σ.var y = .ptr l →
      Step σ { σ with var := upd σ.var x (.ptr (C.stepC a l)) }
  | lab {σ : State V L F} {x y : V} {t : T} :
      P (.lab x y t) → Step σ { σ with var := upd σ.var x (σ.var y) }
  | i2p {σ : State V L F} {x y : V} :
      P (.i2p x y) → σ.var y ≠ .data →
      Step σ { σ with var := upd σ.var x (σ.var y) }
  /-- A pointer made from bytes that never were a pointer: any location. -/
  | forge {σ : State V L F} {x y : V} {l : L} :
      P (.i2p x y) → σ.var y = .data →
      Step σ { σ with var := upd σ.var x (.ptr l) }
  | load {σ : State V L F} {x y : V} {ka : K} {l : L} :
      P (.load x y ka) → σ.var y = .ptr l →
      Step σ { σ with var := upd σ.var x (σ.mem l) }
  | store {σ : State V L F} {x y : V} {ka : K} {l : L} :
      P (.store x ka y) → σ.var x = .ptr l →
      Step σ { σ with mem := upd σ.mem l (σ.var y) }
  | icall {σ : State V L F} {x y : V} {i : Nat} {f : F} :
      P (.icall x i y) → σ.var x = .fn f →
      Step σ { σ with var := upd σ.var (C.formal f i) (σ.var y) }
  | icallRet {σ : State V L F} {r x : V} {f : F} :
      P (.icallRet r x) → σ.var x = .fn f →
      Step σ { σ with var := upd σ.var r (σ.var (C.ret f)) }
  | dcall {σ : State V L F} {x : V} {afn adata : A} {i : Nat} {l : L} {f : F} :
      P (.dcall x afn adata i) → σ.var x = .ptr l →
      σ.mem (C.stepC afn l) = .fn f →
      Step σ { σ with var := upd σ.var (C.formal f i) (σ.mem (C.stepC adata l)) }

/-- Reachable states: all variables hold data, memory is the environment's
initial memory, then any sequence of steps. -/
inductive Reach : State V L F → Prop where
  | init : Reach { var := fun _ => .data, mem := C.mem0 }
  | step {σ σ' : State V L F} : Reach σ → Step C P σ σ' → Reach σ'

end Semantics

/-! ## Keys -/

/-- A key domain: what keys denote, when two keys may share a location, how
an access key narrows a pointer's key, and the key transformers. -/
structure KeyDomain (L A T K : Type) where
  γ : K → L → Prop
  meets : K → K → Prop
  meetK : K → K → K
  fa : A → K → K
  rl : T → K → K

/-! ## Analysis: any solution closed under the rules -/

inductive AVal (K F : Type) where
  | ptr (k : K)
  | fn (f : F)

structure Solution (V A T K F : Type) (D : KeyDomain L A T K)
    (formal : F → Nat → V) (ret : F → V) (envCnt : K → K → Prop)
    (P : Stmt V A T K F → Prop) where
  pts : V → AVal K F → Prop
  cnt : K → AVal K F → Prop
  c_alloc : ∀ {x k}, P (.alloc x k) → pts x (.ptr k)
  c_fnaddr : ∀ {x f}, P (.fnaddr x f) → pts x (.fn f)
  c_copy : ∀ {x y v}, P (.copy x y) → pts y v → pts x v
  c_field : ∀ {x y a k}, P (.field x y a) → pts y (.ptr k) →
    pts x (.ptr (D.fa a k))
  c_lab_ptr : ∀ {x y t k}, P (.lab x y t) → pts y (.ptr k) →
    pts x (.ptr (D.rl t k))
  c_lab_fn : ∀ {x y t f}, P (.lab x y t) → pts y (.fn f) → pts x (.fn f)
  c_i2p : ∀ {x y v}, P (.i2p x y) → pts y v → pts x v
  c_load : ∀ {x y ka k c v}, P (.load x y ka) → pts y (.ptr k) → cnt c v →
    D.meets c (D.meetK k ka) → pts x v
  c_store : ∀ {x y ka k v}, P (.store x ka y) → pts x (.ptr k) → pts y v →
    cnt (D.meetK k ka) v
  c_env : ∀ {c k}, envCnt c k → cnt c (.ptr k)
  c_icall : ∀ {x y i f v}, P (.icall x i y) → pts x (.fn f) → pts y v →
    pts (formal f i) v
  c_icallRet : ∀ {r x f v}, P (.icallRet r x) → pts x (.fn f) →
    pts (ret f) v → pts r v
  c_dcall : ∀ {x afn adata i k c1 f c2 v}, P (.dcall x afn adata i) →
    pts x (.ptr k) → cnt c1 (.fn f) → D.meets c1 (D.fa afn k) →
    cnt c2 v → D.meets c2 (D.fa adata k) → pts (formal f i) v

/-! ## Coverage -/

section Coverage

variable (D : KeyDomain L A T K)

/-- A concrete value is covered by a set of abstract values. -/
def CovV (S : AVal K F → Prop) : Val L F → Prop
  | .data => True
  | .fn f => S (.fn f)
  | .ptr l => ∃ k, S (.ptr k) ∧ D.γ k l

/-- The content of location `l` is covered by some cell whose key holds `l`. -/
def CovM (cnt : K → AVal K F → Prop) (l : L) : Val L F → Prop
  | .data => True
  | .fn f => ∃ c, D.γ c l ∧ cnt c (.fn f)
  | .ptr l' => ∃ c k, D.γ c l ∧ D.γ k l' ∧ cnt c (.ptr k)

end Coverage

/-! ## The rules, as properties of executions -/

section Rules

variable [DecidableEq V] [DecidableEq L]
variable (C : Concrete (K := K) V L F A) (P : Stmt V A T K F → Prop)
variable (D : KeyDomain L A T K) (envCnt : K → K → Prop)

/-- Rule (a): no pointer is made from bytes that never were a pointer. -/
def NoForge : Prop :=
  ∀ σ x y, Reach C P σ → P (.i2p x y) → σ.var y ≠ .data

/-- Rules (b) and (c): every access touches a location inside its key. -/
def AccessAgree : Prop :=
  (∀ σ x y ka l, Reach C P σ → P (.load x y ka) → σ.var y = .ptr l →
      D.γ ka l) ∧
  (∀ σ x y ka l, Reach C P σ → P (.store x ka y) → σ.var x = .ptr l →
      D.γ ka l)

/-- Field steps cover the concrete address arithmetic, at every step that
runs one (GEPs and the two reads of a correlated call). -/
def FieldCover : Prop :=
  (∀ σ x y a l k, Reach C P σ → P (.field x y a) → σ.var y = .ptr l →
      D.γ k l → D.γ (D.fa a k) (C.stepC a l)) ∧
  (∀ σ x afn adata i l k, Reach C P σ → P (.dcall x afn adata i) →
      σ.var x = .ptr l → D.γ k l →
      D.γ (D.fa afn k) (C.stepC afn l) ∧ D.γ (D.fa adata k) (C.stepC adata l))

/-- Instance refinements are faithful: an object passing a labeling point
`t` is one the label `t` denotes (no use after reuse). -/
def Faithful : Prop :=
  ∀ σ x y t l k, Reach C P σ → P (.lab x y t) → σ.var y = .ptr l →
    D.γ k l → D.γ (D.rl t k) l

/-- Allocation sites: an allocation's result lies in its site key. -/
def AllocCover : Prop := ∀ k l, C.isAlloc k l → D.γ k l

/-- `meets` holds whenever two keys share a location (it may hold more). -/
def MeetSound : Prop := ∀ c c' l, D.γ c l → D.γ c' l → D.meets c c'

/-- Narrowing a pointer's key by an access key keeps the shared locations. -/
def MeetKSound : Prop := ∀ k ka l, D.γ k l → D.γ ka l → D.γ (D.meetK k ka) l

/-- The environment holds data and pointers to environment data, never code;
its pointers are described by `envCnt`. -/
def EnvInit : Prop :=
  (∀ l f, C.mem0 l ≠ .fn f) ∧
  (∀ l l', C.mem0 l = .ptr l' → ∃ c k, envCnt c k ∧ D.γ c l ∧ D.γ k l')

end Rules

/-! ## Soundness -/

section Soundness

variable [DecidableEq V] [DecidableEq L]
variable {C : Concrete (K := K) V L F A} {P : Stmt V A T K F → Prop}
variable {D : KeyDomain L A T K} {envCnt : K → K → Prop}

/-- The invariant: every variable and every location is covered. -/
def Inv (S : Solution V A T K F D C.formal C.ret envCnt P)
    (σ : State V L F) : Prop :=
  (∀ x, CovV D (S.pts x) (σ.var x)) ∧ (∀ l, CovM D S.cnt l (σ.mem l))

omit [DecidableEq V] [DecidableEq L] in
theorem covV_of_eq {S T' : AVal K F → Prop} {v : Val L F}
    (h : ∀ a, S a → T' a) : CovV D S v → CovV D T' v := by
  cases v with
  | data => intro _; trivial
  | fn f => exact h _
  | ptr l => exact fun ⟨k, hk, hl⟩ => ⟨k, h _ hk, hl⟩

omit [DecidableEq L] in
/-- Updating one variable with a covered value keeps the variables covered. -/
theorem inv_upd_var (S : Solution V A T K F D C.formal C.ret envCnt P)
    {σ : State V L F} {x : V} {v : Val L F}
    (hI : Inv S σ) (hv : CovV D (S.pts x) v) :
    Inv S { σ with var := upd σ.var x v } := by
  refine ⟨fun z => ?_, hI.2⟩
  show CovV D (S.pts z) (upd σ.var x v z)
  unfold upd
  by_cases h : z = x
  · subst h; simpa using hv
  · simpa [h] using hI.1 z

/-- KEYS ARE SOUND: under the three rules and the key obligations, every
reachable state is covered by every closed solution. No identity roots are
needed: a cell nothing wrote holds data, and by rule (a) data never becomes
a pointer. -/
theorem keys_sound (S : Solution V A T K F D C.formal C.ret envCnt P)
    (hForge : NoForge C P) (hAcc : AccessAgree C P D)
    (hField : FieldCover C P D) (hFaith : Faithful C P D)
    (hAlloc : AllocCover C D) (hMeet : MeetSound D) (hMeetK : MeetKSound D)
    (hEnv : EnvInit C D envCnt) :
    ∀ σ, Reach C P σ → Inv S σ := by
  intro σ hR
  induction hR with
  | init =>
    refine ⟨fun _ => trivial, fun l => ?_⟩
    show CovM D S.cnt l (C.mem0 l)
    cases h0 : C.mem0 l with
    | data => trivial
    | fn f => exact absurd h0 (hEnv.1 l f)
    | ptr l' =>
      obtain ⟨c, k, hck, hc, hk⟩ := hEnv.2 l l' h0
      exact ⟨c, k, hc, hk, S.c_env hck⟩
  | step hR hs ih =>
    rename_i σ σ'
    cases hs with
    | alloc hP hA =>
      exact inv_upd_var S ih ⟨_, S.c_alloc hP, hAlloc _ _ hA⟩
    | fnaddr hP => exact inv_upd_var S ih (S.c_fnaddr hP)
    | copy hP => exact inv_upd_var S ih (covV_of_eq (fun _ => S.c_copy hP) (ih.1 _))
    | field hP hy =>
      rename_i x y a l
      have hc := ih.1 y
      rw [hy] at hc
      obtain ⟨k, hk, hl⟩ := hc
      exact inv_upd_var S ih ⟨_, S.c_field hP hk, hField.1 _ _ _ _ _ _ hR hP hy hl⟩
    | lab hP =>
      rename_i x y t
      apply inv_upd_var S ih
      have hc := ih.1 y
      cases hv : σ.var y with
      | data => trivial
      | fn f => rw [hv] at hc; exact S.c_lab_fn hP hc
      | ptr l =>
        rw [hv] at hc
        obtain ⟨k, hk, hl⟩ := hc
        exact ⟨_, S.c_lab_ptr hP hk, hFaith _ _ _ _ _ _ hR hP hv hl⟩
    | i2p hP _ =>
      exact inv_upd_var S ih (covV_of_eq (fun _ => S.c_i2p hP) (ih.1 _))
    | forge hP hy => exact absurd hy (hForge _ _ _ hR hP)
    | load hP hy =>
      rename_i x y ka l
      apply inv_upd_var S ih
      have hc := ih.1 y
      rw [hy] at hc
      obtain ⟨k, hk, hl⟩ := hc
      have hka := hAcc.1 _ _ _ _ _ hR hP hy
      have hm := hMeetK _ _ _ hl hka
      have hcm := ih.2 l
      cases hv : σ.mem l with
      | data => trivial
      | fn f =>
        rw [hv] at hcm
        obtain ⟨c, hcl, hcnt⟩ := hcm
        exact S.c_load hP hk hcnt (hMeet _ _ _ hcl hm)
      | ptr l' =>
        rw [hv] at hcm
        obtain ⟨c, k', hcl, hk', hcnt⟩ := hcm
        exact ⟨k', S.c_load hP hk hcnt (hMeet _ _ _ hcl hm), hk'⟩
    | store hP hx =>
      rename_i x y ka l
      have hc := ih.1 x
      rw [hx] at hc
      obtain ⟨k, hk, hl⟩ := hc
      have hka := hAcc.2 _ _ _ _ _ hR hP hx
      have hm := hMeetK _ _ _ hl hka
      refine ⟨ih.1, fun l2 => ?_⟩
      show CovM D S.cnt l2 (upd σ.mem l (σ.var y) l2)
      unfold upd
      by_cases h : l2 = l
      · subst h
        rw [ite_eq_left rfl]
        have hcy := ih.1 y
        cases hv : σ.var y with
        | data => trivial
        | fn f => rw [hv] at hcy; exact ⟨_, hm, S.c_store hP hk hcy⟩
        | ptr l' =>
          rw [hv] at hcy
          obtain ⟨k', hk', hl'⟩ := hcy
          exact ⟨_, k', hm, hl', S.c_store hP hk hk'⟩
      · simpa [h] using ih.2 l2
    | icall hP hx =>
      rename_i x y i f
      have hf := ih.1 x
      rw [hx] at hf
      exact inv_upd_var S ih (covV_of_eq (fun _ => S.c_icall hP hf) (ih.1 _))
    | icallRet hP hx =>
      rename_i r x f
      have hf := ih.1 x
      rw [hx] at hf
      exact inv_upd_var S ih (covV_of_eq (fun _ => S.c_icallRet hP hf) (ih.1 _))
    | dcall hP hx hfn =>
      rename_i x afn adata i l f
      apply inv_upd_var S ih
      have hc := ih.1 x
      rw [hx] at hc
      obtain ⟨k, hk, hl⟩ := hc
      obtain ⟨hfnK, hdataK⟩ := hField.2 _ _ _ _ _ _ _ hR hP hx hl
      have hcf := ih.2 (C.stepC afn l)
      rw [hfn] at hcf
      obtain ⟨c1, hc1l, hc1⟩ := hcf
      have hm1 := hMeet _ _ _ hc1l hfnK
      have hcd := ih.2 (C.stepC adata l)
      cases hv : σ.mem (C.stepC adata l) with
      | data => trivial
      | fn g =>
        rw [hv] at hcd
        obtain ⟨c2, hc2l, hc2⟩ := hcd
        exact S.c_dcall hP hk hc1 hm1 hc2 (hMeet _ _ _ hc2l hdataK)
      | ptr l' =>
        rw [hv] at hcd
        obtain ⟨c2, k', hc2l, hk', hc2⟩ := hcd
        exact ⟨k', S.c_dcall hP hk hc1 hm1 hc2 (hMeet _ _ _ hc2l hdataK), hk'⟩

/-- Every function an indirect call actually calls is in its answer. -/
theorem icall_sound (S : Solution V A T K F D C.formal C.ret envCnt P)
    (hForge : NoForge C P) (hAcc : AccessAgree C P D)
    (hField : FieldCover C P D) (hFaith : Faithful C P D)
    (hAlloc : AllocCover C D) (hMeet : MeetSound D) (hMeetK : MeetKSound D)
    (hEnv : EnvInit C D envCnt)
    {σ : State V L F} {x : V} {f : F} (hR : Reach C P σ)
    (hx : σ.var x = .fn f) : S.pts x (.fn f) := by
  have h := (keys_sound S hForge hAcc hField hFaith hAlloc hMeet hMeetK hEnv σ hR).1 x
  rw [hx] at h
  exact h

omit [DecidableEq V] [DecidableEq L] in
/-- COARSENING: a larger `meets` (union-find clusters make it transitive;
presolve and SCC merges coarsen further) is still sound. Merging costs
precision, never soundness. -/
theorem coarsen_sound (D : KeyDomain L A T K) (meets' : K → K → Prop)
    (hle : ∀ c c', D.meets c c' → meets' c c') (hMeet : MeetSound D) :
    MeetSound { D with meets := meets' } :=
  fun c c' l hc hc' => hle _ _ (hMeet c c' l hc hc')

end Soundness

/-! ## Keys as a product: (site, position, instance)

Meet is componentwise and each dimension carries its own obligation:
site by construction, position by `PunFree` and the address arithmetic,
instance by faithfulness. A concrete location projects onto the three
dimensions. -/

section Product

variable {S Pos I : Type}

/-- One dimension: what its keys denote, when two may share a value, and how
an access narrows a pointer's key. -/
structure Dim (X Kd : Type) where
  γd : Kd → X → Prop
  meetsd : Kd → Kd → Prop
  meetKd : Kd → Kd → Kd

def Dim.Sound {X Kd : Type} (d : Dim X Kd) : Prop :=
  (∀ a b x, d.γd a x → d.γd b x → d.meetsd a b) ∧
  (∀ a b x, d.γd a x → d.γd b x → d.γd (d.meetKd a b) x)

/-- Concrete locations project onto (site, position, instance). -/
structure Proj (L S Pos I : Type) where
  site : L → S
  pos : L → Pos
  inst : L → I

variable {KS KP KI : Type}

/-- The product key domain. Field steps act on the position dimension only,
refinements on the instance dimension only. -/
def ProductKey (π : Proj L S Pos I) (dS : Dim S KS) (dP : Dim Pos KP)
    (dI : Dim I KI) (faP : A → KP → KP) (rlI : T → KI → KI) :
    KeyDomain L A T (KS × KP × KI) where
  γ k l := dS.γd k.1 (π.site l) ∧ dP.γd k.2.1 (π.pos l) ∧ dI.γd k.2.2 (π.inst l)
  meets a b := dS.meetsd a.1 b.1 ∧ dP.meetsd a.2.1 b.2.1 ∧ dI.meetsd a.2.2 b.2.2
  meetK a b := (dS.meetKd a.1 b.1, dP.meetKd a.2.1 b.2.1, dI.meetKd a.2.2 b.2.2)
  fa a k := (k.1, faP a k.2.1, k.2.2)
  rl t k := (k.1, k.2.1, rlI t k.2.2)

variable (π : Proj L S Pos I) (dS : Dim S KS) (dP : Dim Pos KP) (dI : Dim I KI)
variable (faP : A → KP → KP) (rlI : T → KI → KI)

theorem product_meetSound (hS : dS.Sound) (hP : dP.Sound) (hI : dI.Sound) :
    MeetSound (ProductKey (A := A) (T := T) π dS dP dI faP rlI) :=
  fun _ _ _ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ =>
    ⟨hS.1 _ _ _ a1 b1, hP.1 _ _ _ a2 b2, hI.1 _ _ _ a3 b3⟩

theorem product_meetKSound (hS : dS.Sound) (hP : dP.Sound) (hI : dI.Sound) :
    MeetKSound (ProductKey (A := A) (T := T) π dS dP dI faP rlI) :=
  fun _ _ _ ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ =>
    ⟨hS.2 _ _ _ a1 b1, hP.2 _ _ _ a2 b2, hI.2 _ _ _ a3 b3⟩

/-- The position obligation: a field step keeps the object (site and
instance) and its position key covers the new position. -/
theorem product_fieldCover {stepC : A → L → L} {a : A} {l : L} {k : KS × KP × KI}
    (hsite : π.site (stepC a l) = π.site l)
    (hinst : π.inst (stepC a l) = π.inst l)
    (hpos : dP.γd k.2.1 (π.pos l) → dP.γd (faP a k.2.1) (π.pos (stepC a l)))
    (hk : (ProductKey π dS dP dI faP rlI).γ k l) :
    (ProductKey (T := T) π dS dP dI faP rlI).γ
      ((ProductKey (T := T) π dS dP dI faP rlI).fa a k) (stepC a l) := by
  obtain ⟨h1, h2, h3⟩ := hk
  exact ⟨hsite ▸ h1, hpos h2, hinst ▸ h3⟩

/-- The instance obligation: a refinement covers the instance it marks. -/
theorem product_faithful {t : T} {l : L} {k : KS × KP × KI}
    (hinst : dI.γd k.2.2 (π.inst l) → dI.γd (rlI t k.2.2) (π.inst l))
    (hk : (ProductKey (A := A) π dS dP dI faP rlI).γ k l) :
    (ProductKey (A := A) π dS dP dI faP rlI).γ
      ((ProductKey (A := A) π dS dP dI faP rlI).rl t k) l := by
  obtain ⟨h1, h2, h3⟩ := hk
  exact ⟨h1, h2, hinst h3⟩

end Product

end Keys
