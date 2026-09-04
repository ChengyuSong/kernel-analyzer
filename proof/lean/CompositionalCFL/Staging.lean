import CompositionalCFL.Core

/-!
# Staging backfill (2026-09-04 modeling-policy audit)

Model-level statements for optimizations that previously ran on
byte-identity gates alone (GAPS.md backfill ledger). As everywhere
in this development, the value is in WHERE the hypotheses sit: each
theorem's hypothesis list is the deployment condition the
implementation must discharge (by construction, by certificate, or
by a stated assumption).

1. `prune_sound` — bidi-prune root pruning (FI): an origin whose
   partition-cone misses every dispatch class contributes no
   answer. Hypotheses: the partition-cone over-approximates
   derivation reach (`cone_covers`), and every answer is derived at
   a dispatch class. The #43 incident is the contrapositive lesson:
   `cone_covers` must hold for the CURRENT graph — a cone computed
   on an earlier wiring does not satisfy it, which is why the cone
   oracle re-admits at wiring time.
2. `mark_skip_exact` — the cluster-mark join fast path: a
   conservative cache (marks only ever assert TRUE memberships)
   makes probe-skipping invisible to the closure. One-directional
   by design: a MISSING mark costs a redundant probe, never an
   answer.
3. `memo_exact` — presolve-once: a pure function of an unchanged
   input may be computed once. The content is the hypothesis:
   `unchanged` is exactly what a stale spill directory violates.
4. `adopt_sound` — per-run summary adoption is a PRECISION
   mechanism (measured −89,189 at 5.18 FI), so its obligation is
   soundness, not exactness: replacing a callee's body-wiring by
   atom-wiring preserves answer soundness iff the atoms cover
   every realizable transfer of the callee (`atoms_complete`).
   That hypothesis is the proposer's completeness contract.
-/

namespace Staging

open CompositionalCFL (Set)

/-! ## 1. Bidi-prune root irrelevance -/

/-- Abstract pruning model: `Cls` = bidirected partition classes,
`cone C` = the d/f-cone of class `C` (set of classes), `dispatch C`
= C contains a dispatch (fptr-read) cell, `Deriv o C` = the solve
derives origin `o`'s fact at some cell of `C`, `Ans o` = origin
`o` appears in some answer. -/
structure PruneModel (Origin Cls : Type) where
  cls : Origin → Cls
  cone : Cls → Set Cls
  dispatch : Cls → Prop
  Deriv : Origin → Cls → Prop
  Ans : Origin → Prop
  /-- answers arise only from derivations at dispatch classes -/
  ans_at_dispatch : ∀ o, Ans o → ∃ C, dispatch C ∧ Deriv o C
  /-- the partition-cone over-approximates derivation reach, FOR
  THE GRAPH BEING SOLVED (the #43 hypothesis: recompute or
  re-admit when wiring changes) -/
  cone_covers : ∀ o C, Deriv o C → cone (cls o) C

/-- An origin whose cone contains no dispatch class appears in no
answer: pruning it cannot remove an answer. -/
theorem prune_sound {Origin Cls : Type} (M : PruneModel Origin Cls)
    (o : Origin) (h : ∀ C, M.cone (M.cls o) C → ¬ M.dispatch C) :
    ¬ M.Ans o := by
  intro hAns
  obtain ⟨C, hD, hDer⟩ := M.ans_at_dispatch o hAns
  exact h C (M.cone_covers o C hDer) hD

/-! ## 2. Cluster-mark join fast path -/

/-- Join-skipping model: `member c` = cell `c` already belongs to
the origin's cluster (ground truth at probe time); `mark c` = the
monotone mirror consulted by the fast path; `effect c` = the
closure contribution the probed join would make; joins are
idempotent: a member's join contributes nothing new. -/
structure MarkModel (Cell : Type) where
  member : Cell → Prop
  mark : Cell → Prop
  effect : Cell → Prop
  /-- conservativeness: marks only ever assert true memberships -/
  mark_sound : ∀ c, mark c → member c
  /-- idempotence: joining an existing member has no effect -/
  member_noop : ∀ c, member c → ¬ effect c

/-- Skipping the probe on a marked cell loses no closure effect.
One-directional by construction: nothing is claimed for unmarked
members (they cost a redundant probe, never an answer). -/
theorem mark_skip_exact {Cell : Type} (M : MarkModel Cell)
    (c : Cell) (hm : M.mark c) : ¬ M.effect c :=
  M.member_noop c (M.mark_sound c hm)

/-! ## 3. Presolve-once -/

/-- Reusing a pure function's result is exact exactly when the
input is unchanged. Stated despite triviality because the
hypothesis is the operational content: a later round presenting a
DIFFERENT graph (or a stale spill directory presenting an earlier
round's state) is precisely `g' ≠ g`, and no reuse is licensed. -/
theorem memo_exact {G P : Type} (presolve : G → P) (g g' : G)
    (unchanged : g' = g) : presolve g' = presolve g := by
  rw [unchanged]

/-! ## 4. Adoption soundness -/

/-- Adoption model: at an adopted callee, `Flow e` = runtime value
flow `e` exists through the callee; `bodyModels e` = the callee's
body-wiring models `e`; `atomModels e` = the adopted summary's
atom-wiring models `e`. -/
structure AdoptModel (E : Type) where
  Flow : E → Prop
  bodyModels : E → Prop
  atomModels : E → Prop
  /-- the body-wiring is sound (the baseline analysis property) -/
  body_sound : ∀ e, Flow e → bodyModels e
  /-- proposer completeness: every realizable flow the body models
  is modeled by some adopted atom — the completeness contract the
  proposer's gates must discharge -/
  atoms_complete : ∀ e, Flow e → bodyModels e → atomModels e

/-- Replacing body-wiring by atom-wiring preserves soundness: every
runtime flow remains modeled. Precision may change (atoms may model
strictly fewer non-realizable flows — the measured −89,189), which
is the point of adopting. -/
theorem adopt_sound {E : Type} (M : AdoptModel E) :
    ∀ e, M.Flow e → M.atomModels e := by
  intro e hf
  exact M.atoms_complete e hf (M.body_sound e hf)

end Staging

/-! ## 5. Incremental cross-iteration solving (`incr_exact`)

The theorem the 2026-09-04 divergence was missing. Model: rules as
instances (premise set, conclusion); a resolution iteration grows
the instance set (Rn ⊆ R'). From-scratch = closure under R'. The
incremental worklist retains Fn and fires an instance only when
some premise is FRESH (not in Fn) — retained facts are never
re-processed — plus an explicit seed set D0.

The load-bearing hypothesis is `delta_seeds_complete`: every NEW
instance (in R' but not Rn) all of whose premises are OLD facts
must have its conclusion seeded. Instances with a fresh premise
fire on their own; old-premises-only instances of OLD rules
already fired into Fn. The 518 miss is exactly this clause: newly
wired call edges (instances in R' \ Rn) connecting old
actual-facts to old formal-cells — no fresh premise, so nothing
triggers unless seeded, and the touched-window seeding missed the
callback-argument edge kinds. The repair is now specified: the
implementation's seed enumeration must cover R' \ Rn instance
kinds with all-old premises, and the certificate's full rescan
(C0–C5) checks the resulting closure per run. -/

namespace Incr

variable {F : Type}

/-- Rule instances: premise set and conclusion. -/
structure Inst (F : Type) where
  prem : F → Prop
  concl : F

/-- Closure of seed set `A` under instance set `R`. -/
inductive Cl (R : Inst F → Prop) (A : F → Prop) : F → Prop
  | seed {a} : A a → Cl R A a
  | step {i} : R i → (∀ p, i.prem p → Cl R A p) → Cl R A i.concl

/-- Fresh-triggered closure: retained facts `Fn` and seeds `D0` are
in; an instance fires only if some premise lies outside `Fn`
(the delta-worklist discipline: old facts are never re-offered). -/
inductive ICl (R : Inst F → Prop) (Fn D0 : F → Prop) : F → Prop
  | retained {a} : Fn a → ICl R Fn D0 a
  | seed {a} : D0 a → ICl R Fn D0 a
  | step {i} : R i → (∀ p, i.prem p → ICl R Fn D0 p) →
      (∃ p, i.prem p ∧ ¬ Fn p) → ICl R Fn D0 i.concl

theorem incr_exact (Rn R' : Inst F → Prop) (Fn D0 : F → Prop)
    (mono : ∀ i, Rn i → R' i)
    -- Fn is the previous iteration's closure:
    (fn_sound : ∀ a, Fn a → Cl Rn (fun _ => False) a)
    (fn_closed : ∀ i, Rn i → (∀ p, i.prem p → Fn p) → Fn i.concl)
    -- seeds are sound:
    (d0_sound : ∀ a, D0 a → Cl R' (fun _ => False) a)
    -- THE obligation (violated at 518): new instances with
    -- all-old premises must be seeded:
    (delta_seeds_complete : ∀ i, R' i → ¬ Rn i →
        (∀ p, i.prem p → Fn p) → Fn i.concl ∨ D0 i.concl) :
    ∀ a, ICl R' Fn D0 a ↔ Cl R' (fun _ => False) a := by
  -- Fn ⊆ scratch closure (monotone lift of the old closure).
  have fn_in : ∀ a, Fn a → Cl R' (fun _ => False) a := by
    intro a ha
    have lift : ∀ b, Cl Rn (fun _ => False) b →
        Cl R' (fun _ => False) b := by
      intro b hb
      induction hb with
      | seed h => exact absurd h (fun h => h)
      | step hR _ ih => exact Cl.step (mono _ hR) ih
    exact lift a (fn_sound a ha)
  intro a
  constructor
  · -- soundness: incremental derives only scratch facts
    intro h
    induction h with
    | retained h => exact fn_in _ h
    | seed h => exact d0_sound _ h
    | step hR _ _ ih => exact Cl.step hR ih
  · -- completeness: every scratch fact is incrementally derived
    intro h
    induction h with
    | seed h => exact absurd h (fun h => h)
    | step hR hp ih =>
      rename_i i
      by_cases hfresh : ∃ p, i.prem p ∧ ¬ Fn p
      · exact ICl.step hR ih hfresh
      · have hall : ∀ p, i.prem p → Fn p := fun p hp =>
          Classical.byContradiction (fun hn => hfresh ⟨p, hp, hn⟩)
        by_cases hRn : Rn i
        · exact ICl.retained (fn_closed i hRn hall)
        · rcases delta_seeds_complete i hR hRn hall with h | h
          · exact ICl.retained h
          · exact ICl.seed h

end Incr
