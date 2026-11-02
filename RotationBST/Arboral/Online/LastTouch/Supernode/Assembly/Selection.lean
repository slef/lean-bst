module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Proofs
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Select.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Parent selection is an exact rotation execution whose retained holes
remain canonical. Costs are those of the shared splitter, without charging
again for the possibly large attached child subtrees. -/
theorem selectParent_spec {P : Finset Point} {lo : Nat} {state : State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (keys : Finset Nat) :
    (selectParent state children lo keys).1.Valid P lo ∧
      Rotations (Nested.layer state children).tree (selectParent state children lo keys).1.region.tree
        (selectParent state children lo keys).2 ∧
      (selectParent state children lo keys).2 ≤ 6014 * state.size := by
  have balanced : state.HeightValid := by cases represented; assumption
  have arity : children.length = state.size + 1 := by cases represented; assumption
  let gaps := fun (j : Nat) => ((children.map Nested.tree)[j]?).getD Tree.nil
  let ranks := touchedRanks state.tree.size gaps 0 lo keys
  have bounds : ∀ key ∈ ranks, key < (intervalTree (some state)).size := by
    intro key member
    exact Finset.mem_range.mp (Finset.mem_filter.mp member).1
  have spec := selectKeys_spec (some state) ranks balanced bounds
  have size := spec.2.1.size_eq
  have fits : (selectKeys (some state) ranks).1.tree.size = state.size := by
    simpa only [intervalTree, state_size] using size.symm
  have valid := assemblePartition_valid represented _ spec.1 0 (by omega)
  have materialized := assemblePartition_tree (selectKeys (some state) ranks).1 children 0 (by omega)
  have steps := (withGaps_rotations spec.2.1 gaps 0).1
  change (assemblePartition (selectKeys (some state) ranks).1 children 0).Valid P lo ∧ _
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, gapWeight] using valid
  · simp only [Nested.tree, selectParent]
    change Rotations (withGaps state.tree gaps 0).tree _ _
    rw [materialized]
    exact steps
  · have cost := spec.2.2.2
    simp only [intervalTree, state_size] at cost
    change (selectKeys (some state) ranks).2 ≤ _
    omega

end RotationBST.Arboral.Online.Supernode
