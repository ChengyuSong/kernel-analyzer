import CompositionalCFL.Core

/-!
# Answer-level channel soundness (2026-08 precision levers)

Machine-checks the three levers shipped in the rendezvous campaign,
each against an abstract runtime-event semantics. The value of the
formalization is WHERE the hypotheses sit:

1. `clamp_sound` — the regfield fn-table clamp
   (`--cfl-regfield-apply`): `answer(site) := answer(site) ∩ table`.
   Sound under TWO obligations: writer-side closure (every runtime
   dispatch through the key's field hits the table — the CLOSED
   certificate) and reader-side attribution (every clamped site really
   reads that field). The implementation certifies the first; the
   second rests on GEP-derived site keys (a structural surrogate) —
   `clamp_needs_attribution` exhibits a model where dropping it makes
   the clamped answer unsound (the drbg-shaped hazard, 2026-08-25).
2. `objclamp_sound` — the object-population re-founding: certify WHICH
   objects can occupy the field and clamp with the union of their
   slots. The reader obligation weakens to "the site reads SOME slot
   of some certified object" — slot attribution drops out entirely,
   which is the design's safety argument.
3. `nulljoin_sound` — null-cell join hygiene: cluster joins keyed by
   cells no runtime execution realizes (store-through-null is UB) can
   be skipped without losing any realizable alias.
4. `skipwiring_sound` — transfer-free summaries at indirectly-resolved
   callsites: skipping arg/ret wiring for a callee certified to
   transfer nothing is sound at ANY resolution of the site — at a
   wrong resolution the callee is never invoked there (wiring models
   no realizable flow), at the right one the certificate applies.
-/

namespace Channels

open CompositionalCFL (Set)

/-! ## 1. Field-table clamping (regfield) -/

/-- Abstract dispatch semantics: `Ev s f` = at runtime, callsite `s`
indirectly calls `f`. `readsKey s` = the fptr dispatched at `s` was
loaded from the certified field key. `table f` = the witnessed
registration population of that key. -/
structure DispatchModel (Site Fn : Type) where
  Ev : Site → Fn → Prop
  readsKey : Site → Prop
  table : Set Fn

/-- Writer-side CLOSED certificate: every runtime dispatch through the
key's field calls a table member (all stores witnessed). -/
def DispatchModel.Closed {Site Fn : Type} (M : DispatchModel Site Fn) : Prop :=
  ∀ s f, M.Ev s f → M.readsKey s → M.table f

/-- An answer map is sound when it covers every runtime event. -/
def SoundAnswer {Site Fn : Type} (M : DispatchModel Site Fn)
    (A : Site → Set Fn) : Prop :=
  ∀ s f, M.Ev s f → A s f

/-- The clamp: intersect at sites the analyzer attributed to the key. -/
def clamp {Site Fn : Type} (M : DispatchModel Site Fn)
    (clamped : Site → Prop) (A : Site → Set Fn) : Site → Set Fn :=
  fun s f => A s f ∧ (clamped s → M.table f)

/-- Regfield soundness: writer closure + reader attribution
(`clamped ⊆ readsKey`) preserve answer soundness. Both hypotheses are
load-bearing; the implementation discharges `Closed` with the hazard
counters and `attr` only via the GEP site key (surrogate). -/
theorem clamp_sound {Site Fn : Type} (M : DispatchModel Site Fn)
    (clamped : Site → Prop) (A : Site → Set Fn)
    (hA : SoundAnswer M A) (hC : M.Closed)
    (attr : ∀ s, clamped s → M.readsKey s) :
    SoundAnswer M (clamp M clamped A) := by
  intro s f hev
  exact ⟨hA s f hev, fun hcl => hC s f hev (attr s hcl)⟩

/-- The attribution hypothesis cannot be dropped: with one site, one
fn, an event at a NON-key-reading site, and an empty table, the
writer certificate holds vacuously yet the clamp erases the true
target. This is the drbg-shaped hazard made formal: a clamp landing
on a mis-keyed site is unsound even with a perfect table. -/
theorem clamp_needs_attribution :
    ∃ (M : DispatchModel Unit Unit) (clamped : Unit → Prop)
      (A : Unit → Set Unit),
      SoundAnswer M A ∧ M.Closed ∧
      ¬ SoundAnswer M (clamp M clamped A) := by
  refine ⟨⟨fun _ _ => True, fun _ => False, fun _ => False⟩,
          fun _ => True, fun _ _ => True, ?_, ?_, ?_⟩
  · intro s f _; trivial
  · intro s f _ h; exact h
  · intro h
    exact (h () () trivial).2 trivial

/-! ## 2. Object-population clamping (the re-founding) -/

/-- Object-level model: the field holds OBJECTS; `holds s o` = at
runtime, the object dispatched through at site `s` is `o`; `slotFns o`
= the fns readable from any slot of `o` (initializer facts). -/
structure ObjDispatchModel (Site Obj Fn : Type) where
  Ev : Site → Fn → Prop
  holds : Site → Obj → Prop
  pop : Set Obj            -- certified object population
  slotFns : Obj → Set Fn   -- fns in any slot of the object

/-- Object-closure certificate: every runtime dispatch at a site goes
through some object of the certified population, calling one of its
slot fns. Note the site obligation is only "dispatches through SOME
certified object" — no slot identity anywhere. -/
def ObjDispatchModel.Closed {Site Obj Fn : Type}
    (M : ObjDispatchModel Site Obj Fn) (siteOk : Site → Prop) : Prop :=
  ∀ s f, M.Ev s f → siteOk s →
    ∃ o, M.holds s o ∧ M.pop o ∧ M.slotFns o f

/-- fns-of(O): the slot-agnostic clamp table. -/
def ObjDispatchModel.fnsOf {Site Obj Fn : Type}
    (M : ObjDispatchModel Site Obj Fn) : Set Fn :=
  fun f => ∃ o, M.pop o ∧ M.slotFns o f

/-- Object-population clamp soundness: sites need only the weak claim
`siteOk` (reads some slot of some certified object); slot
misattribution is harmless BY CONSTRUCTION — the table is the union
over all slots, so a wrong slot still lands inside `fnsOf`. -/
theorem objclamp_sound {Site Obj Fn : Type}
    (M : ObjDispatchModel Site Obj Fn) (clamped : Site → Prop)
    (A : Site → Set Fn)
    (hA : ∀ s f, M.Ev s f → A s f)
    (hC : M.Closed (fun s => clamped s))
    : ∀ s f, M.Ev s f →
        (A s f ∧ (clamped s → M.fnsOf f)) := by
  intro s f hev
  refine ⟨hA s f hev, fun hcl => ?_⟩
  obtain ⟨o, _, hpop, hslot⟩ := hC s f hev hcl
  exact ⟨o, hpop, hslot⟩

/-! ## 3. Null-cell join hygiene -/

/-- Join model: cluster joins are keyed by cells; `realizes k` = some
runtime execution stores AND loads through the cell keyed `k` (the
only way a join models a real flow). Store-through-null is UB — no
execution realizes the null cell's key. -/
structure JoinModel (Key : Type) where
  realizes : Key → Prop
  isNull : Key → Prop
  null_unrealizable : ∀ k, isNull k → ¬ realizes k

/-- A join set suffices when it covers every realizable key. Skipping
null-keyed joins preserves sufficiency: the skipped keys are exactly
ones no execution realizes. -/
theorem nulljoin_sound {Key : Type} (M : JoinModel Key)
    (J : Set Key) (hJ : ∀ k, M.realizes k → J k) :
    ∀ k, M.realizes k → (fun k' => J k' ∧ ¬ M.isNull k') k := by
  intro k hr
  refine ⟨hJ k hr, fun hn => M.null_unrealizable k hn hr⟩

/-! ## 4. Transfer-free summaries at indirectly-resolved sites -/

/-- Wiring model: `Flow e` = runtime value flow `e` exists; a wiring
edge `(s, c, e)` models flow `e` introduced by callee `c` invoked at
site `s`. `invoked s c` = the runtime call at `s` actually reaches
`c`; `transferFree c` = the certificate: `c` introduces no flows. -/
structure WiringModel (Site Callee E : Type) where
  Flow : E → Prop
  models : Site → Callee → E → Prop
  invoked : Site → Callee → Prop
  transferFree : Callee → Prop
  flow_needs_call : ∀ s c e, Flow e → models s c e → invoked s c
  cert : ∀ s c e, transferFree c → invoked s c → models s c e → ¬ Flow e

/-- Skipping wiring for a transfer-free callee is sound at ANY
resolution quality of the site: a runtime flow modeled by the skipped
wiring would require the callee to be invoked there (wrong resolution
= never invoked = no such flow) and the certificate kills the invoked
case. Hence no runtime flow is modeled ONLY by skipped wiring. -/
theorem skipwiring_sound {Site Callee E : Type}
    (M : WiringModel Site Callee E) (s : Site) (c : Callee)
    (hTF : M.transferFree c) :
    ∀ e, M.Flow e → ¬ M.models s c e := by
  intro e hf hm
  exact M.cert s c e hTF (M.flow_needs_call s c e hf hm) hm hf

/-! ## 5. Rodata-table reads and the stride union (2026-08-28/29)

The rodata channel clamps `fn = load(gep(const_table, idx))` with the
table's initializer contents — certificate-free, because a constant
object's cells are its initializer (assumption recorded in GAPS.md:
rodata immutability). With a VARIABLE index the element is unknown,
so the sound table is the UNION over the index residue class:
`stride_union_sound`. The falsified variant (reading element 0 only —
the GT 79->90 regression, nfnetlink/asn1) is `element0_unsound`:
a machine-checked reminder that an unknown selector demands the
union, mirroring `clamp_needs_attribution`'s role for site keys. -/

/-- A const table: slot contents per element index (the initializer
denotation; `none` = null slot). Runtime dispatch selects SOME
element `i` and calls the fn in its slot. -/
structure RodataModel (I Fn : Type) where
  slot : I → Option Fn

/-- The stride-union table: everything any element's slot holds. -/
def RodataModel.unionTable {I Fn : Type} (M : RodataModel I Fn) :
    Set Fn :=
  fun f => ∃ i, M.slot i = some f

/-- Stride-union soundness: whatever element the runtime index
selects, its slot fn is in the union table. -/
theorem stride_union_sound {I Fn : Type} (M : RodataModel I Fn)
    (i : I) (f : Fn) (h : M.slot i = some f) : M.unionTable f :=
  ⟨i, h⟩

/-- The element-0 table is NOT sound under an unknown selector: with
two elements holding distinct fns, clamping to element 0's slot drops
element 1's true target. (Bool as the index; `false` plays element
0.) -/
theorem element0_unsound :
    ∃ (M : RodataModel Bool Bool) (i : Bool) (f : Bool),
      M.slot i = some f ∧
      ¬ (fun g => M.slot false = some g) f := by
  refine ⟨⟨fun i => some i⟩, true, true, rfl, ?_⟩
  intro h
  exact Bool.noConfusion (Option.some.inj h)

/-! ## 6. Interior population members (row 5) as member shift

An interior member `(G, base, stride)` contributes, at dispatch slot
`off`, the fns of `G`'s initializer at offsets `base + k*stride +
off`. Soundness is `stride_union_sound` composed with an offset
shift; the both-sides-var refusal keeps the residue class
well-defined (two independent strides would make the class the whole
object — still sound as a union but not stated here; the
implementation refuses instead). -/

end Channels
