import CompositionalCFL.FlowsTo

/-!
# Origin-equivalence bundles (docs/origin-bundles-design.md)

The bundled solver represents a set of co-traveling origins by one
fact id. Two theorems justify it:

- `bundle_exact`: given a representative map `q` on origins whose
  classes are CLOSURE-ROW-EQUAL (every member's fact row equals its
  representative's), the solve that mints only representatives and
  seeds each representative at every member's node derives exactly
  the per-origin closure, member by member. The interesting case is
  joins: a bundled witness allows MIXED members on the two cell
  parents; row equality collapses the mix back to a single witness.

- `row_determined`: the runtime epoch test. Two minted origins whose
  PARTIAL-STATE rows (the carried base, which contains their seeds)
  are equal have equal closure rows — no solver rule distinguishes
  origins beyond their seeds and their rows. This is what lets the
  implementation bundle at any drain checkpoint from a full-state
  hash, with closure-row equality (the `bundle_exact` hypothesis)
  as the consequence.

What stays BELOW this abstraction (engineering-verified, see
GAPS.md): the rid renumbering pass (bijection on plane bits), the
cluster-key remap and its L1 equal-or-absent assertion, harvest
expansion of bundle bits to leaves, and the exclusion list (prot
rids, measurement flags) that keeps the per-rid side condition true.
-/

namespace FlowsToCFL

/-- Bundle seeding as base facts: representative `q n` carries a
shift-zero fact at EVERY member node `n` (the implementation's plane
rewrite: member columns fold into the bundle column, which therefore
holds every member's seed bit). -/
def bundleBase (M : ShiftMonoid) {N : Type} (minted : N → Prop)
    (q : N → N) : N → Shift M → N → Prop :=
  fun b c x => c = some M.zero ∧ minted x ∧ q x = b

/-- Representative root set: only class representatives are minted in
the bundled solve. -/
def bundleMinted {N : Type} (minted : N → Prop) (q : N → N) :
    N → Prop :=
  fun b => ∃ n, minted n ∧ q n = b

/-- Closure-row equality between a member and its representative:
the `bundle_exact` side condition, established for the epoch test by
`row_determined`. -/
def RowEq (M : ShiftMonoid) {N : Type} (G : FGraph N M.S)
    (minted : N → Prop) (q : N → N) : Prop :=
  ∀ n, minted n → ∀ c x,
    SDeriv M G minted (noBase M N) n c x ↔
    SDeriv M G minted (noBase M N) (q n) c x

/-- Bundled solve → per-origin solve, for EVERY member of the class.
Row equality discharges the two places bundling is coarser: member
seeds (the bundle column holds all members' seed bits) and mixed-
member join witnesses. -/
theorem bundle_sound (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {q : N → N}
    (hqm : ∀ n, minted n → minted (q n))
    (hqi : ∀ n, minted n → q (q n) = q n)
    (hrows : RowEq M G minted q) :
    ∀ {b : N} {c : Shift M} {x : N},
      SDeriv M G (bundleMinted minted q) (bundleBase M minted q) b c x →
      ∀ m, minted m → q m = b →
        SDeriv M G minted (noBase M N) m c x := by
  intro b c x h
  induction h with
  | ofBase hB =>
      -- bundle column holds member n's seed; any member m of the same
      -- class reaches n because row(m) = row(q m) = row(q n) ∋ (0, n)
      rcases hB with ⟨hc, hn, hqn⟩
      intro m hm hqmb
      subst hc
      have hn0 : SDeriv M G minted (noBase M N) _ (some M.zero) _ :=
        SDeriv.seed _ hn
      have h1 := (hrows _ hn _ _).mp hn0
      rw [hqn, ← hqmb] at h1
      exact (hrows m hm _ _).mpr h1
  | seed b hb =>
      -- representative's own seed: member m reaches node b = q m since
      -- row(m) = row(q m) ∋ (0, q m)
      rcases hb with ⟨n, hn, hqn⟩
      intro m hm hqmb
      have hrep : minted (q n) := hqm n hn
      rw [hqn] at hrep
      have hb0 : SDeriv M G minted (noBase M N) b (some M.zero) b :=
        SDeriv.seed b hrep
      have h1 := (hrows m hm _ _).mpr (by rw [hqmb]; exact hb0)
      exact h1
  | step_a _ hE ih =>
      intro m hm hqmb; exact .step_a (ih m hm hqmb) hE
  | step_f _ hE ih =>
      intro m hm hqmb; exact .step_f (ih m hm hqmb) hE
  | step_fx _ hE ih =>
      intro m hm hqmb; exact .step_fx (ih m hm hqmb) hE
  | join_e hEp hEq hbw _ _ _ ihp ihq ihx =>
      -- bundled witness class bw: instantiate both sides with the
      -- REPRESENTATIVE q n (minted, in its own class by idempotence)
      -- — mixed members collapse to one witness
      intro m hm hqmb
      rcases hbw with ⟨n, hn, hqn⟩
      have hrepm : minted (q n) := hqm n hn
      have hrepw : q (q n) = _ := (hqi n hn).trans hqn
      exact .join_e hEp hEq hrepm (ihp (q n) hrepm hrepw)
        (ihq (q n) hrepm hrepw) (ihx m hm hqmb)
  | join_xl hEp hEq hbw _ _ _ ihp ihq ihx =>
      intro m hm hqmb
      rcases hbw with ⟨n, hn, hqn⟩
      have hrepm : minted (q n) := hqm n hn
      have hrepw : q (q n) = _ := (hqi n hn).trans hqn
      exact .join_xl hEp hEq hrepm (ihp (q n) hrepm hrepw)
        (ihq (q n) hrepm hrepw) (ihx m hm hqmb)
  | join_xr hEp hEq hbw _ _ _ ihp ihq ihx =>
      intro m hm hqmb
      rcases hbw with ⟨n, hn, hqn⟩
      have hrepm : minted (q n) := hqm n hn
      have hrepw : q (q n) = _ := (hqi n hn).trans hqn
      exact .join_xr hEp hEq hrepm (ihp (q n) hrepm hrepw)
        (ihq (q n) hrepm hrepw) (ihx m hm hqmb)

/-- Per-origin solve → bundled solve: bundling only weakens
preconditions (any member seed is a bundle base fact; any witness is
a member of its own class). No row hypothesis needed. -/
theorem bundle_complete (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {q : N → N} :
    ∀ {m : N} {c : Shift M} {x : N},
      SDeriv M G minted (noBase M N) m c x →
      SDeriv M G (bundleMinted minted q) (bundleBase M minted q)
        (q m) c x := by
  intro m c x h
  induction h with
  | ofBase hB => exact hB.elim
  | seed n hn => exact .ofBase ⟨rfl, hn, rfl⟩
  | step_a _ hE ih => exact .step_a ih hE
  | step_f _ hE ih => exact .step_f ih hE
  | step_fx _ hE ih => exact .step_fx ih hE
  | join_e hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_e hEp hEq ⟨_, hw, rfl⟩ ihp ihq ihx
  | join_xl hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_xl hEp hEq ⟨_, hw, rfl⟩ ihp ihq ihx
  | join_xr hEp hEq hw _ _ _ ihp ihq ihx =>
      exact .join_xr hEp hEq ⟨_, hw, rfl⟩ ihp ihq ihx

/-- BUNDLE EXACTNESS: under closure-row equality, the bundled closure
expanded to any member IS that member's per-origin closure. -/
theorem bundle_exact (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {q : N → N}
    (hqm : ∀ n, minted n → minted (q n))
    (hqi : ∀ n, minted n → q (q n) = q n)
    (hrows : RowEq M G minted q)
    {m : N} (hm : minted m) {c : Shift M} {x : N} :
    SDeriv M G (bundleMinted minted q) (bundleBase M minted q)
      (q m) c x ↔
    SDeriv M G minted (noBase M N) m c x := by
  constructor
  · intro h; exact bundle_sound M hqm hqi hrows h m hm rfl
  · exact bundle_complete M

/-- THE EPOCH TEST: two minted origins whose carried-base rows are
EQUAL (as (shift, node) sets) — with each base containing at least
its own origin's seed, which any post-seeding checkpoint satisfies —
have equal closure rows. No solver rule distinguishes origins beyond
seeds and rows, so the derivation relabels origin `m₁` to `m₂`
wholesale; third-party witnesses are untouched. This discharges the
`RowEq` hypothesis of `bundle_exact` from the implementation's
full-state hash at a drain checkpoint. -/
theorem row_determined (M : ShiftMonoid) {N : Type} {G : FGraph N M.S}
    {minted : N → Prop} {base : N → Shift M → N → Prop}
    {m₁ m₂ : N}
    (hseed₁ : base m₁ (some M.zero) m₁)
    (hbase : ∀ c x, base m₁ c x ↔ base m₂ c x) :
    ∀ {c : Shift M} {x : N},
      SDeriv M G minted base m₁ c x →
      SDeriv M G minted base m₂ c x := by
  intro c x h
  -- strengthen: facts of ANY origin are preserved, with m₁'s facts
  -- relabeled to m₂ and every other origin's facts kept verbatim —
  -- witnesses inside joins may themselves be m₁
  suffices H : ∀ {o : N} {c : Shift M} {x : N},
      SDeriv M G minted base o c x →
      SDeriv M G minted base o c x ∧
      (o = m₁ → SDeriv M G minted base m₂ c x) by
    exact (H h).2 rfl
  intro o c x h
  induction h with
  | ofBase hB =>
      refine ⟨.ofBase hB, fun ho => ?_⟩
      subst ho
      exact .ofBase ((hbase _ _).mp hB)
  | seed n hn =>
      refine ⟨.seed n hn, fun ho => ?_⟩
      subst ho
      exact .ofBase ((hbase _ _).mp hseed₁)
  | step_a _ hE ih =>
      exact ⟨.step_a ih.1 hE, fun ho => .step_a (ih.2 ho) hE⟩
  | step_f _ hE ih =>
      exact ⟨.step_f ih.1 hE, fun ho => .step_f (ih.2 ho) hE⟩
  | step_fx _ hE ih =>
      exact ⟨.step_fx ih.1 hE, fun ho => .step_fx (ih.2 ho) hE⟩
  | join_e hEp hEq hw _ _ _ ihp ihq ihx =>
      exact ⟨.join_e hEp hEq hw ihp.1 ihq.1 ihx.1,
             fun ho => .join_e hEp hEq hw ihp.1 ihq.1 (ihx.2 ho)⟩
  | join_xl hEp hEq hw _ _ _ ihp ihq ihx =>
      exact ⟨.join_xl hEp hEq hw ihp.1 ihq.1 ihx.1,
             fun ho => .join_xl hEp hEq hw ihp.1 ihq.1 (ihx.2 ho)⟩
  | join_xr hEp hEq hw _ _ _ ihp ihq ihx =>
      exact ⟨.join_xr hEp hEq hw ihp.1 ihq.1 ihx.1,
             fun ho => .join_xr hEp hEq hw ihp.1 ihq.1 (ihx.2 ho)⟩

/-- Symmetric corollary: equal bases give equal closure rows. -/
theorem row_determined_iff (M : ShiftMonoid) {N : Type}
    {G : FGraph N M.S} {minted : N → Prop}
    {base : N → Shift M → N → Prop} {m₁ m₂ : N}
    (hseed₁ : base m₁ (some M.zero) m₁)
    (hseed₂ : base m₂ (some M.zero) m₂)
    (hbase : ∀ c x, base m₁ c x ↔ base m₂ c x)
    {c : Shift M} {x : N} :
    SDeriv M G minted base m₁ c x ↔ SDeriv M G minted base m₂ c x :=
  ⟨row_determined M hseed₁ hbase,
   row_determined M hseed₂ (fun c x => (hbase c x).symm)⟩

end FlowsToCFL
