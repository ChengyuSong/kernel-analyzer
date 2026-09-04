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
