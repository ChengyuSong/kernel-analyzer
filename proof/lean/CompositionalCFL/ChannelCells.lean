import CompositionalCFL.Core

/-!
# Channel cells: pairwise-witnessed M vs transitive clusters

The flows-to grammar's memory-alias relation is pairwise-witnessed:
a store's content reaches a load iff ONE shared (origin, shift) key
witnesses both dereferences (`M ::= -d V d`, one origin per
derivation; shifts fold into the key). The solver realizes M with
union-find clusters keyed (origin, shift); union-find equivalence
is TRANSITIVE, so a cell witnessing two keys coalesces their
clusters and content crosses WITHOUT a shared witness — a
derivation the grammar does not have.

MODELING PREMISE (stated in docs/channel-cells-design.md): `keys c`
is the set of (origin, shift) pairs the cell's base V-flows to —
exactly the witness set the grammar's M rule quantifies over. The
model is single-hop; multi-hop movement composes through the outer
closure identically under both semantics, so containment and
strictness lift hop-wise.

Results:
- `chanflow_iff_pairflow`: routing store-cell → channel(k) →
  load-cell realizes exactly the grammar's M — the channel-cells
  implementation computes the spec by construction.
- `pair_le_cluster`: the cluster semantics over-approximates the
  grammar — switching to channels is removal-only (the one-sided
  gate is the right gate).
- `cluster_exceeds_pair`: strictness, in the measured nm-new shape
  (writer {k2}, conduit {k1,k2}, reader {k1}: cluster flows,
  grammar does not).
- `rw_conduit_leaks`: a read-write cell wired in BOTH directions
  re-creates the transitive leak through itself — the v1 rule that
  both-cells keep merge semantics (or are split) is load-bearing,
  not conservatism.
-/

namespace ChannelCells

open CompositionalCFL (Set)

/-- Per-access cells with their witness keys. `isStore`/`isLoad` =
the cell's role from the build (a store cell receives its value,
a load cell feeds its result). -/
structure CellModel (C K : Type) where
  keys : C → Set K
  isStore : C → Prop
  isLoad : C → Prop

variable {C K : Type} (M : CellModel C K)

/-- The grammar's M, content direction: one shared witness key. -/
def PairFlow (c d : C) : Prop :=
  M.isStore c ∧ M.isLoad d ∧ ∃ k, M.keys c k ∧ M.keys d k

/-- Channel routing, as the implementation wires it: a store cell
feeds channel k for each of its keys; channel k feeds each load
cell keyed k. -/
def toChan (c : C) (k : K) : Prop := M.isStore c ∧ M.keys c k
def fromChan (k : K) (d : C) : Prop := M.isLoad d ∧ M.keys d k
def ChanFlow (c d : C) : Prop := ∃ k, toChan M c k ∧ fromChan M k d

/-- The channel graph realizes exactly the grammar's M. -/
theorem chanflow_iff_pairflow (c d : C) :
    ChanFlow M c d ↔ PairFlow M c d := by
  constructor
  · rintro ⟨k, ⟨hs, hck⟩, hl, hdk⟩
    exact ⟨hs, hl, k, hck, hdk⟩
  · rintro ⟨hs, hl, k, hck, hdk⟩
    exact ⟨k, ⟨hs, hck⟩, hl, hdk⟩

/-- Key-sharing between two cells (undirected: union-find merges
regardless of access role). -/
def SharesKey (c d : C) : Prop := ∃ k, M.keys c k ∧ M.keys d k

/-- Union-find cluster identity: the transitive closure of
key-sharing. (Symmetry is built into `SharesKey`; reflexivity is
irrelevant for flows.) -/
inductive Linked : C → C → Prop
  | base {c d} : SharesKey M c d → Linked c d
  | trans {c d e} : Linked c d → Linked d e → Linked c e

/-- Content flow under the cluster implementation: store and load
cells in one union-find class exchange content. -/
def ClusterFlow (c d : C) : Prop :=
  M.isStore c ∧ M.isLoad d ∧ Linked M c d

/-- The cluster semantics over-approximates the grammar: switching
to channel routing only removes flows (one-sided gate). -/
theorem pair_le_cluster (c d : C) :
    PairFlow M c d → ClusterFlow M c d := by
  rintro ⟨hs, hl, k, hck, hdk⟩
  exact ⟨hs, hl, .base ⟨k, hck, hdk⟩⟩

/-! ## Strictness: the measured nm-new shape -/

private inductive C3 where
  | writer | conduit | reader

private def m3 : CellModel C3 Bool where
  keys
    | .writer => fun k => k = false            -- {k2}
    | .conduit => fun _ => True                -- {k1, k2}
    | .reader => fun k => k = true             -- {k1}
  isStore c := c = .writer
  isLoad c := c = .reader

/-- A conduit cell witnessing both keys makes the cluster carry
writer→reader with NO shared witness: the transitive data structure
exceeds the pairwise grammar. This is the nm-new countermodel (an
identity-origin web of conduit cells glued 400+ keys across all 14
shifts into one cluster). -/
theorem cluster_exceeds_pair :
    ClusterFlow m3 .writer .reader ∧ ¬ PairFlow m3 .writer .reader := by
  constructor
  · refine ⟨rfl, rfl, .trans (d := C3.conduit) ?_ ?_⟩
    · exact .base ⟨false, rfl, trivial⟩
    · exact .base ⟨true, trivial, rfl⟩
  · rintro ⟨-, -, k, hw, hr⟩
    cases k
    · exact Bool.noConfusion hr
    · exact Bool.noConfusion hw

/-! ## The read-write conduit hazard (v1 both-cells rule) -/

/-- Channel routing where one designated cell `rw` is wired in BOTH
directions (in from its channels and out to them). -/
def RwChanFlow (rw : C) (c d : C) : Prop :=
  ChanFlow M c d ∨
  (∃ k k', toChan M c k ∧ M.keys rw k ∧ M.keys rw k' ∧ fromChan M k' d)

/-- Wiring a read-write cell bidirectionally re-creates the
transitive leak through that cell: content crosses two DIFFERENT
keys. Hence v1 keeps merge semantics for both-cells (equivalent
pooling, honestly accounted) or splits them — never bidirectional
channel edges. -/
theorem rw_conduit_leaks :
    RwChanFlow m3 .conduit .writer .reader ∧
    ¬ ChanFlow m3 .writer .reader := by
  constructor
  · exact .inr ⟨false, true, ⟨rfl, rfl⟩, trivial, trivial, rfl, rfl⟩
  · intro h
    exact (cluster_exceeds_pair).2 ((chanflow_iff_pairflow m3 _ _).mp h)

end ChannelCells
