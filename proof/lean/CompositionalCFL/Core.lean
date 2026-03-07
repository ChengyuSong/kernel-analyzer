namespace CompositionalCFL

/-- Nonterminals from the default P2 grammar in `Global.h`. -/
inductive NT where
  | M | DV | V | MAM | Mq | MAs | AMs | MA | AM
  deriving DecidableEq, Repr

/-- Edge labels used by the CFL constraints. -/
inductive Label where
  | a
  | na
  | d
  | nd
  deriving DecidableEq, Repr

/-- Boundary categories currently required by compositional merging and
summary-edge wiring in the implementation. -/
inductive CoreBoundaryKind where
  | func
  | arg
  | ret
  | vararg
  | glob
  | icall
  | larg
  | lret
  | lvararg
  | icallarg
  | icallret
  deriving DecidableEq, Repr

/-- Optional boundary categories used to improve precision/convergence. -/
inductive PrecisionBoundaryKind where
  | gptr
  | gderef
  deriving DecidableEq, Repr

/-- Boundary symbol kind used by composition-level merging. -/
inductive BoundaryKind where
  | core (k : CoreBoundaryKind)
  | precision (k : PrecisionBoundaryKind)
  deriving DecidableEq, Repr

/-- Predicate distinguishing minimal soundness-critical symbols from extras. -/
def BoundaryKind.isCore : BoundaryKind → Bool
  | .core _ => true
  | .precision _ => false

/-- Labeled directed edge. -/
structure LEdge (N : Type) where
  src : N
  lbl : Label
  dst : N
  deriving Repr

/-- Local set alias (`α → Prop`) to avoid extra dependencies. -/
abbrev Set (α : Type) := α → Prop

instance {α : Type} : Membership α (Set α) where
  mem s a := s a

instance {α : Type} : HasSubset (Set α) where
  Subset s t := ∀ a, s a → t a

/-- A graph is a set of labeled edges. -/
abbrev Graph (N : Type) := Set (LEdge N)

/-- Reachability judgment following the default grammar in `Global.h`:

M   -> DV d
DV  -> -d V
V   -> MAM AMs
MAM -> MAs Mq
Mq  -> eps | M
MAs -> eps | MAs MA
MA  -> Mq -a
AMs -> eps | AMs AM
AM  -> a Mq
-/
inductive Reach {N : Type} (G : Graph N) : N → NT → N → Prop where
  | m_dv_d {u x v : N} :
      Reach G u NT.DV x →
      ({ src := x, lbl := Label.d, dst := v } : LEdge N) ∈ G →
      Reach G u NT.M v
  | dv_nd_v {u x v : N} :
      ({ src := u, lbl := Label.nd, dst := x } : LEdge N) ∈ G →
      Reach G x NT.V v →
      Reach G u NT.DV v
  | v_mam_ams {u x v : N} :
      Reach G u NT.MAM x →
      Reach G x NT.AMs v →
      Reach G u NT.V v
  | mam_mas_mq {u x v : N} :
      Reach G u NT.MAs x →
      Reach G x NT.Mq v →
      Reach G u NT.MAM v
  | mq_eps {u : N} :
      Reach G u NT.Mq u
  | mq_m {u v : N} :
      Reach G u NT.M v →
      Reach G u NT.Mq v
  | mas_eps {u : N} :
      Reach G u NT.MAs u
  | mas_cons {u x v : N} :
      Reach G u NT.MAs x →
      Reach G x NT.MA v →
      Reach G u NT.MAs v
  | ma_mq_na {u x v : N} :
      Reach G u NT.Mq x →
      ({ src := x, lbl := Label.na, dst := v } : LEdge N) ∈ G →
      Reach G u NT.MA v
  | ams_eps {u : N} :
      Reach G u NT.AMs u
  | ams_cons {u x v : N} :
      Reach G u NT.AMs x →
      Reach G x NT.AM v →
      Reach G u NT.AMs v
  | am_a_mq {u x v : N} :
      ({ src := u, lbl := Label.a, dst := x } : LEdge N) ∈ G →
      Reach G x NT.Mq v →
      Reach G u NT.AM v

/-- Remap a labeled edge through a node map `f`. -/
def mapEdge {N1 N2 : Type} (f : N1 → N2) (e : LEdge N1) : LEdge N2 :=
  { src := f e.src, lbl := e.lbl, dst := f e.dst }

/-- Edge-preserving simulation from `G₁` to `G₂`. -/
def GraphHom {N1 N2 : Type} (f : N1 → N2) (G₁ : Graph N1) (G₂ : Graph N2) : Prop :=
  ∀ e, e ∈ G₁ → mapEdge f e ∈ G₂

/-- Edge-wise graph inclusion. -/
abbrev GraphLe {N : Type} (G₁ G₂ : Graph N) : Prop := G₁ ⊆ G₂

/-- Identity map is a graph homomorphism whenever the source graph is included
in the target graph. -/
theorem graphHom_id_of_subset
    {N : Type}
    {G₁ G₂ : Graph N}
    (hSub : GraphLe G₁ G₂) :
    GraphHom (fun x => x) G₁ G₂ := by
  intro e hEdge
  simpa [GraphLe, mapEdge] using hSub e hEdge

/-- Quotient graph obtained by remapping all edges through `q`.
Set semantics already performs deduplication. -/
def quotientGraph {N Q : Type} (G : Graph N) (q : N → Q) : Graph Q :=
  fun eQ => ∃ eN, eN ∈ G ∧ mapEdge q eN = eQ

/-- Composition graph obtained by remapping all quotient edges through `merge`.
Again, set semantics gives deduplication for free. -/
def composedGraph {Q C : Type} (Gq : Graph Q) (merge : Q → C) : Graph C :=
  fun eC => ∃ eQ, eQ ∈ Gq ∧ mapEdge merge eQ = eC

/-- Union of two edge sets. -/
def graphUnion {N : Type} (G₁ G₂ : Graph N) : Graph N :=
  fun e => e ∈ G₁ ∨ e ∈ G₂

/-- Add self-seed edges for boundary nodes so edge-isolated boundaries remain
materialized (singleton SCCs) after remap/compression. This models the
`pinnedBoundaryNodes` + seeded self-edge fix in `solveAndCompressPerTU`. -/
def pinBoundaryNodes
    {N : Type}
    (seedLbl : Label)
    (isBoundary : N → Prop)
    (G : Graph N) : Graph N :=
  fun e =>
    e ∈ G ∨
    ∃ n : N, isBoundary n ∧ e = ({ src := n, lbl := seedLbl, dst := n } : LEdge N)

/-- Pinning is extensive: original edges are preserved. -/
theorem pinBoundaryNodes_extensive
    {N : Type}
    (seedLbl : Label)
    (isBoundary : N → Prop)
    (G : Graph N) :
    GraphLe G (pinBoundaryNodes seedLbl isBoundary G) := by
  intro e hEdge
  exact Or.inl hEdge

/-- Every pinned boundary node gets a seed self-edge. -/
theorem pinBoundaryNodes_seed_self
    {N : Type}
    (seedLbl : Label)
    (isBoundary : N → Prop)
    {n : N}
    (hBoundary : isBoundary n) :
    ({ src := n, lbl := seedLbl, dst := n } : LEdge N) ∈
      pinBoundaryNodes seedLbl isBoundary (fun _ => False) := by
  exact Or.inr ⟨n, hBoundary, rfl⟩

/-- Summary-edge generation rule over the current graph. -/
abbrev SummaryRule (N : Type) := Graph N → Graph N

/-- One iterative augmentation step used by compositional re-solving:
keep existing edges and add summary edges inferred from the current graph. -/
def summaryStep {N : Type} (rule : SummaryRule N) : Graph N → Graph N :=
  fun G => graphUnion G (rule G)

/-- Directed bridge relation used to emit summary assignment edges. -/
abbrev AssignBridge (N : Type) := Graph N → N → N → Prop

/-- Summary edge pair emitted by compositional call/arg propagation:
`a` models assign and `na` models inverse-assign. -/
def assignEdgePair {N : Type} (actual target : N) : Graph N :=
  fun e =>
    e = { src := actual, lbl := Label.a, dst := target } ∨
    e = { src := target, lbl := Label.na, dst := actual }

/-- Generic summary rule that emits assign-edge pairs for bridge witnesses.
This models `addAssignEdgePair` in `runCompositionalSolve`, instantiated with a
bridge relation such as `icallarg -> (arg/larg/vararg/lvararg)`. -/
def assignBridgeRule {N : Type} (bridge : AssignBridge N) : SummaryRule N :=
  fun G e => ∃ actual target, bridge G actual target ∧ e ∈ assignEdgePair actual target

/-- Monotonicity of assign-pair generation, assuming monotone bridge discovery. -/
theorem assignBridgeRule_mono
    {N : Type}
    (bridge : AssignBridge N)
    (hBridgeMono :
      ∀ {G₁ G₂ : Graph N}, GraphLe G₁ G₂ →
      ∀ {actual target : N}, bridge G₁ actual target → bridge G₂ actual target) :
    ∀ {G₁ G₂ : Graph N}, GraphLe G₁ G₂ →
      GraphLe (assignBridgeRule bridge G₁) (assignBridgeRule bridge G₂) := by
  intro G₁ G₂ hSub e hEdge
  rcases hEdge with ⟨actual, target, hBridge, hPair⟩
  exact ⟨actual, target, hBridgeMono hSub hBridge, hPair⟩

/-- Build an iterative step package from a monotone summary rule. -/
structure IterStep (N : Type) where
  step : Graph N → Graph N
  monotone : ∀ {G₁ G₂ : Graph N}, GraphLe G₁ G₂ → GraphLe (step G₁) (step G₂)
  extensive : ∀ G : Graph N, GraphLe G (step G)

/-- Any monotone summary rule yields an extensive + monotone step. -/
def mkSummaryIterStep
    {N : Type}
    (rule : SummaryRule N)
    (hMono : ∀ {G₁ G₂ : Graph N}, GraphLe G₁ G₂ → GraphLe (rule G₁) (rule G₂)) :
    IterStep N where
  step := summaryStep rule
  monotone := by
    intro G₁ G₂ hSub e hEdge
    rcases hEdge with hL | hR
    · exact Or.inl (hSub e hL)
    · exact Or.inr (hMono hSub e hR)
  extensive := by
    intro G e hEdge
    exact Or.inl hEdge

/-- n-step iteration from seed graph `G0`. -/
def iterGraph {N : Type} (it : IterStep N) (G0 : Graph N) : Nat → Graph N
  | 0 => G0
  | n + 1 => it.step (iterGraph it G0 n)

/-- Iterative closure: edges present after some finite number of iterations. -/
def iterClosure {N : Type} (it : IterStep N) (G0 : Graph N) : Graph N :=
  fun e => ∃ n : Nat, e ∈ iterGraph it G0 n

/-- Seed graph is included in the iterative closure. -/
theorem seed_subset_iterClosure
    {N : Type}
    (it : IterStep N)
    (G0 : Graph N) :
    GraphLe G0 (iterClosure it G0) := by
  intro e hEdge
  exact ⟨0, hEdge⟩

/-- The first augmented graph (`step G0`) is included in the iterative closure. -/
theorem first_step_subset_iterClosure
    {N : Type}
    (it : IterStep N)
    (G0 : Graph N) :
    GraphLe (it.step G0) (iterClosure it G0) := by
  intro e hEdge
  exact ⟨1, by simpa [iterGraph] using hEdge⟩

/-- `q` is a graph homomorphism from `G` into its quotient image. -/
theorem quotientGraph_hom
    {N Q : Type}
    (G : Graph N)
    (q : N → Q) :
    GraphHom q G (quotientGraph G q) := by
  intro e hEdge
  exact ⟨e, hEdge, rfl⟩

/-- `merge` is a graph homomorphism from `Gq` into its composed image. -/
theorem composedGraph_hom
    {Q C : Type}
    (Gq : Graph Q)
    (merge : Q → C) :
    GraphHom merge Gq (composedGraph Gq merge) := by
  intro e hEdge
  exact ⟨e, hEdge, rfl⟩

/-- Core simulation lemma: CFL reachability is preserved by graph homomorphism. -/
theorem reach_map
    {N1 N2 : Type}
    {G₁ : Graph N1}
    {G₂ : Graph N2}
    (f : N1 → N2)
    (hHom : GraphHom f G₁ G₂)
    {u v : N1}
    {X : NT}
    (h : Reach G₁ u X v) :
    Reach G₂ (f u) X (f v) := by
  induction h with
  | m_dv_d h1 hEdge ih1 =>
      exact Reach.m_dv_d ih1 (hHom _ hEdge)
  | dv_nd_v hEdge h2 ih2 =>
      exact Reach.dv_nd_v (hHom _ hEdge) ih2
  | v_mam_ams h1 h2 ih1 ih2 =>
      exact Reach.v_mam_ams ih1 ih2
  | mam_mas_mq h1 h2 ih1 ih2 =>
      exact Reach.mam_mas_mq ih1 ih2
  | mq_eps =>
      exact Reach.mq_eps
  | mq_m h1 ih1 =>
      exact Reach.mq_m ih1
  | mas_eps =>
      exact Reach.mas_eps
  | mas_cons h1 h2 ih1 ih2 =>
      exact Reach.mas_cons ih1 ih2
  | ma_mq_na h1 hEdge ih1 =>
      exact Reach.ma_mq_na ih1 (hHom _ hEdge)
  | ams_eps =>
      exact Reach.ams_eps
  | ams_cons h1 h2 ih1 ih2 =>
      exact Reach.ams_cons ih1 ih2
  | am_a_mq hEdge h2 ih2 =>
      exact Reach.am_a_mq (hHom _ hEdge) ih2

/-- Reachability is monotone under graph inclusion. -/
theorem reach_mono
    {N : Type}
    {G₁ G₂ : Graph N}
    (hSub : GraphLe G₁ G₂)
    {u v : N}
    {X : NT}
    (h : Reach G₁ u X v) :
    Reach G₂ u X v := by
  have hHom : GraphHom (fun x => x) G₁ G₂ := graphHom_id_of_subset hSub
  simpa using (reach_map (fun x => x) hHom h)

/-- Soundness theorem schema for compositional analysis.

Interpretation:
- `Gmono` is the monolithic graph.
- `Gcomp` is the composed graph.
- `q` maps monolithic nodes to composed representatives.
- `hSim` is the proof obligation produced by your composition pipeline:
  every monolithic edge is simulated in the composed graph under `q`.

Once you prove `hSim` from your concrete TU-compression + boundary-merge
construction, soundness is immediate from `reach_map`.
-/
theorem compositional_sound
    {Nmono Ncomp : Type}
    (Gmono : Graph Nmono)
    (Gcomp : Graph Ncomp)
    (q : Nmono → Ncomp)
    (hSim : GraphHom q Gmono Gcomp)
    {u v : Nmono}
    {X : NT}
    (hReach : Reach Gmono u X v) :
    Reach Gcomp (q u) X (q v) :=
  reach_map q hSim hReach

/-- If a post-processing phase only adds edges to a composed graph, soundness
is preserved by monotonicity. This models iterative compositional re-solving. -/
theorem compositional_sound_iterative
    {Nmono Ncomp : Type}
    (Gmono : Graph Nmono)
    (Gone : Graph Ncomp)
    (Giter : Graph Ncomp)
    (q : Nmono → Ncomp)
    (hSim : GraphHom q Gmono Gone)
    (hGrow : GraphLe Gone Giter)
    {u v : Nmono}
    {X : NT}
    (hReach : Reach Gmono u X v) :
    Reach Giter (q u) X (q v) := by
  have hOne : Reach Gone (q u) X (q v) :=
    compositional_sound Gmono Gone q hSim hReach
  exact reach_mono hGrow hOne

/-- If composition is sound before boundary pinning, it remains sound after
pinning because pinning only adds edges. This models the per-TU fix that seeds
self-edges for edge-isolated boundary nodes so they survive compression. -/
theorem compositional_sound_with_pinned_boundaries
    {Nmono Ncomp : Type}
    (Gmono : Graph Nmono)
    (Gcomp : Graph Ncomp)
    (q : Nmono → Ncomp)
    (hSim : GraphHom q Gmono Gcomp)
    (seedLbl : Label)
    (isBoundary : Ncomp → Prop)
    {u v : Nmono}
    {X : NT}
    (hReach : Reach Gmono u X v) :
    Reach (pinBoundaryNodes seedLbl isBoundary Gcomp) (q u) X (q v) := by
  have hBase : Reach Gcomp (q u) X (q v) :=
    compositional_sound Gmono Gcomp q hSim hReach
  exact reach_mono (pinBoundaryNodes_extensive seedLbl isBoundary Gcomp) hBase

/-- Running an extensive iterative closure on top of a sound one-shot composed
graph remains sound. -/
theorem compositional_sound_iterClosure
    {Nmono Ncomp : Type}
    (Gmono : Graph Nmono)
    (Gseed : Graph Ncomp)
    (it : IterStep Ncomp)
    (q : Nmono → Ncomp)
    (hSim : GraphHom q Gmono Gseed)
    {u v : Nmono}
    {X : NT}
    (hReach : Reach Gmono u X v) :
    Reach (iterClosure it Gseed) (q u) X (q v) := by
  have hSeed : Reach Gseed (q u) X (q v) :=
    compositional_sound Gmono Gseed q hSim hReach
  exact reach_mono (seed_subset_iterClosure it Gseed) hSeed

/-- Specialization of iterative soundness to assign-pair summary rules.
This captures the compositional icall-argument propagation pattern where
summary edges are wired as `a`/`na` pairs. -/
theorem compositional_sound_assignBridge_iterClosure
    {Nmono Ncomp : Type}
    (Gmono : Graph Nmono)
    (Gseed : Graph Ncomp)
    (bridge : AssignBridge Ncomp)
    (hBridgeMono :
      ∀ {G₁ G₂ : Graph Ncomp}, GraphLe G₁ G₂ →
      ∀ {actual target : Ncomp}, bridge G₁ actual target → bridge G₂ actual target)
    (q : Nmono → Ncomp)
    (hSim : GraphHom q Gmono Gseed)
    {u v : Nmono}
    {X : NT}
    (hReach : Reach Gmono u X v) :
    Reach
      (iterClosure
        (mkSummaryIterStep (assignBridgeRule bridge)
          (assignBridgeRule_mono bridge hBridgeMono))
        Gseed)
      (q u) X (q v) := by
  let it : IterStep Ncomp :=
    mkSummaryIterStep (assignBridgeRule bridge)
      (assignBridgeRule_mono bridge hBridgeMono)
  exact compositional_sound_iterClosure Gmono Gseed it q hSim hReach

/-- Explicit model of per-TU quotienting (e.g., V-SCC compression). -/
structure PerTUQuotient (N Q : Type) where
  /-- TU-local (pre-compression) graph. -/
  Gtu : Graph N
  /-- TU-local compressed graph. -/
  Gquot : Graph Q
  /-- Quotient map from original nodes to compressed representatives. -/
  q : N → Q
  /-- Every TU edge is simulated in the quotient graph. -/
  q_hom : GraphHom q Gtu Gquot

/-- Canonical per-TU quotient package built from `quotientGraph`. -/
def mkPerTUQuotient
    {N Q : Type}
    (Gtu : Graph N)
    (q : N → Q) : PerTUQuotient N Q where
  Gtu := Gtu
  Gquot := quotientGraph Gtu q
  q := q
  q_hom := quotientGraph_hom Gtu q

/-- Explicit model of boundary-based composition/merge. -/
structure BoundaryMerge (Q C B : Type) where
  /-- Input graph after per-TU quotienting. -/
  Gquot : Graph Q
  /-- Output graph after boundary merging/composition. -/
  Gcomp : Graph C
  /-- Merge map from quotient nodes to composed representatives. -/
  merge : Q → C
  /-- Optional boundary symbol attached to each quotient node. -/
  symbol : Q → Option B
  /-- If two nodes carry the same boundary symbol, they collapse to one rep. -/
  boundary_sound : ∀ {x y : Q}, symbol x = symbol y → merge x = merge y
  /-- Every quotient edge is simulated in the composed graph. -/
  merge_hom : GraphHom merge Gquot Gcomp

/-- Canonical boundary-merge package built from `composedGraph`.
`boundary_sound` remains an explicit proof obligation because it depends on the
symbol-equality policy used by the concrete merger (e.g., union-find). -/
def mkBoundaryMerge
    {Q C B : Type}
    (Gquot : Graph Q)
    (merge : Q → C)
    (symbol : Q → Option B)
    (hBoundary : ∀ {x y : Q}, symbol x = symbol y → merge x = merge y) :
    BoundaryMerge Q C B where
  Gquot := Gquot
  Gcomp := composedGraph Gquot merge
  merge := merge
  symbol := symbol
  boundary_sound := hBoundary
  merge_hom := composedGraph_hom Gquot merge

/-- Union-find style boundary merger:
- `rep` is the chosen representative function after unions.
- `rep_idem` models root stability (`find (find x) = find x`).
- `same_symbol_same_rep` is the key correctness invariant for boundary merging. -/
structure UnionFindMerge (Q B : Type) where
  rep : Q → Q
  symbol : Q → Option B
  rep_idem : ∀ x : Q, rep (rep x) = rep x
  same_symbol_same_rep : ∀ {x y : Q}, symbol x = symbol y → rep x = rep y

/-- Boundary-soundness follows from the union-find invariant. -/
theorem boundary_sound_of_unionfind
    {Q B : Type}
    (uf : UnionFindMerge Q B)
    {x y : Q}
    (hEq : uf.symbol x = uf.symbol y) :
    uf.rep x = uf.rep y :=
  uf.same_symbol_same_rep hEq

/-- Build a `BoundaryMerge` directly from a union-find style representative map. -/
def mkBoundaryMergeFromUF
    {Q B : Type}
    (Gquot : Graph Q)
    (uf : UnionFindMerge Q B) :
    BoundaryMerge Q Q B where
  Gquot := Gquot
  Gcomp := composedGraph Gquot uf.rep
  merge := uf.rep
  symbol := uf.symbol
  boundary_sound := by
    intro x y hEq
    exact boundary_sound_of_unionfind uf hEq
  merge_hom := composedGraph_hom Gquot uf.rep

/-- Convenience lemma exposing the boundary merge relation. -/
theorem merged_of_boundary_eq
    {Q C B : Type}
    (bm : BoundaryMerge Q C B)
    {x y : Q}
    (hEq : bm.symbol x = bm.symbol y) :
    bm.merge x = bm.merge y :=
  bm.boundary_sound hEq

/-- Per-TU quotienting followed by boundary merge yields a simulation from
the original TU graph into the composed graph. -/
theorem quotient_then_merge_hom
    {N Q C B : Type}
    (qt : PerTUQuotient N Q)
    (bm : BoundaryMerge Q C B)
    (hSame : qt.Gquot = bm.Gquot) :
    GraphHom (fun n => bm.merge (qt.q n)) qt.Gtu bm.Gcomp := by
  intro e hEdge
  have hQ : mapEdge qt.q e ∈ qt.Gquot := qt.q_hom e hEdge
  have hQ' : mapEdge qt.q e ∈ bm.Gquot := by
    simpa [hSame] using hQ
  have hC : mapEdge bm.merge (mapEdge qt.q e) ∈ bm.Gcomp := bm.merge_hom _ hQ'
  simpa [mapEdge] using hC

/-- Soundness theorem with explicit per-TU quotient + boundary merge layers. -/
theorem compositional_sound_two_stage
    {N Q C B : Type}
    (qt : PerTUQuotient N Q)
    (bm : BoundaryMerge Q C B)
    (hSame : qt.Gquot = bm.Gquot)
    {u v : N}
    {X : NT}
    (hReach : Reach qt.Gtu u X v) :
    Reach bm.Gcomp (bm.merge (qt.q u)) X (bm.merge (qt.q v)) := by
  have hHom : GraphHom (fun n => bm.merge (qt.q n)) qt.Gtu bm.Gcomp :=
    quotient_then_merge_hom qt bm hSame
  exact reach_map (fun n => bm.merge (qt.q n)) hHom hReach

/-- Two-stage theorem lifted through an additional iterative closure over the
composed graph. This captures "compress first, then iterate globally". -/
theorem compositional_sound_two_stage_iterClosure
    {N Q C B : Type}
    (qt : PerTUQuotient N Q)
    (bm : BoundaryMerge Q C B)
    (it : IterStep C)
    (hSame : qt.Gquot = bm.Gquot)
    {u v : N}
    {X : NT}
    (hReach : Reach qt.Gtu u X v) :
    Reach (iterClosure it bm.Gcomp) (bm.merge (qt.q u)) X (bm.merge (qt.q v)) := by
  have hBase : Reach bm.Gcomp (bm.merge (qt.q u)) X (bm.merge (qt.q v)) :=
    compositional_sound_two_stage qt bm hSame hReach
  exact reach_mono (seed_subset_iterClosure it bm.Gcomp) hBase

/-!
## Bug-catcher model: dropping intra-SCC terminal self-loops is unsound

This models the exact design pitfall fixed in commit
`083dc4debb42c6105db7299ca9bbd3410821d562`: after quotienting, dropping the
`d`, `-d`, `a`, `-a` self-loops of a collapsed SCC can destroy valid `M`/`V`
derivations.
-/

inductive DemoNode where
  | x
  | s
  deriving DecidableEq, Repr

/-- Monolithic graph: `x -nd-> s` and `s -d-> s`. -/
def GmonoDemo : Graph DemoNode :=
  fun e =>
    e = { src := DemoNode.x, lbl := Label.nd, dst := DemoNode.s } ∨
    e = { src := DemoNode.s, lbl := Label.d, dst := DemoNode.s }

/-- Bad compressed graph design: the `d` self-loop at `s` is dropped. -/
def GdropDemo : Graph DemoNode :=
  fun e =>
    e = { src := DemoNode.x, lbl := Label.nd, dst := DemoNode.s }

theorem mono_demo_v_ss : Reach GmonoDemo DemoNode.s NT.V DemoNode.s := by
  have hMAM : Reach GmonoDemo DemoNode.s NT.MAM DemoNode.s :=
    Reach.mam_mas_mq Reach.mas_eps Reach.mq_eps
  exact Reach.v_mam_ams hMAM Reach.ams_eps

theorem mono_demo_m_xs : Reach GmonoDemo DemoNode.x NT.M DemoNode.s := by
  have hDV : Reach GmonoDemo DemoNode.x NT.DV DemoNode.s :=
    Reach.dv_nd_v (by
      unfold GmonoDemo
      exact Or.inl rfl) mono_demo_v_ss
  exact Reach.m_dv_d hDV (by
    unfold GmonoDemo
    exact Or.inr rfl)

theorem gdrop_no_d_edge {u v : DemoNode} :
    ({ src := u, lbl := Label.d, dst := v } : LEdge DemoNode) ∉ GdropDemo := by
  intro hIn
  unfold GdropDemo at hIn
  cases hIn

theorem drop_demo_no_m_xs : ¬ Reach GdropDemo DemoNode.x NT.M DemoNode.s := by
  intro hM
  cases hM with
  | m_dv_d _ hD =>
      exact gdrop_no_d_edge hD

/-- Dropping the self-loop breaks edge simulation (`GraphHom`) outright. -/
theorem drop_demo_not_graph_hom : ¬ GraphHom id GmonoDemo GdropDemo := by
  intro hHom
  have hEdge :
      ({ src := DemoNode.s, lbl := Label.d, dst := DemoNode.s } : LEdge DemoNode) ∈ GmonoDemo := by
    unfold GmonoDemo
    exact Or.inr rfl
  have hMapped := hHom _ hEdge
  have hMapped' :
      ({ src := DemoNode.s, lbl := Label.d, dst := DemoNode.s } : LEdge DemoNode) ∈ GdropDemo := by
    simpa [mapEdge] using hMapped
  exact gdrop_no_d_edge hMapped'

/-- Concrete unsoundness witness for the bad compression design. -/
theorem drop_demo_unsound :
    ∃ q : DemoNode → DemoNode,
      Reach GmonoDemo DemoNode.x NT.M DemoNode.s ∧
      ¬ Reach GdropDemo (q DemoNode.x) NT.M (q DemoNode.s) := by
  refine ⟨id, mono_demo_m_xs, ?_⟩
  simpa using drop_demo_no_m_xs

end CompositionalCFL
