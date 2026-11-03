module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Proofs
public import RotationBST.Models.Rotation.Connectivity.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem rebalance_unchanged {state : State} (valid : state.HeightValid) : rebalance state = (state, 0) := by
  simp only [rebalance, valid.2.2, and_self, ite_true]

theorem rebalance_spec (state : State) (left : state.left.Valid) (right : state.right.Valid) :
    (rebalance state).1.HeightValid ∧ Rotations state.tree (rebalance state).1.tree (rebalance state).2 ∧
      (rebalance state).2 ≤ 12 * max state.left.height state.right.height + 6 := by
  by_cases ready : state.left.height ≤ state.right.height + 1 ∧ state.right.height ≤ state.left.height + 1
  · simp only [rebalance, ready, and_self, ite_true]
    exact ⟨⟨left, right, ready⟩, .refl, by omega⟩
  · have joined := Multiway.Join.compact_balance left right
    have sizes := Multiway.Join.compact_size state.left.height state.right.height state.left.tree state.right.tree
    have positive : (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).tree ≠ .nil := by
      intro empty
      rw [empty, size] at sizes
      omega
    have convertedLeft := (conversion_rotations state.left.tree).symm.inLeft
      (r := (maximumView state.right.tree).tree)
    have convertedRight := (maximum_rotations state.right.tree).symm.inRight (l := state.left.tree.binary)
    have joinSteps := Multiway.Join.compact_rotations state.left.height state.right.height state.left.tree state.right.tree
    have establish := fromRoot_rotations
      (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).height _ positive
    have steps := ((convertedLeft.append convertedRight).append joinSteps).append establish
    have initialized := fromRoot_valid joined.1
    have leftCost := conversion_cost left
    have rightCost := maximum_cost right
    have joinCost := Multiway.Join.compact_cost state.left.height state.right.height state.left.tree state.right.tree
    have initCost := fromRoot_cost joined.1
    simp only [rebalance, ready, ite_false]
    exact ⟨initialized, steps, by omega⟩

theorem rebalance_size (state : State) (left : state.left.Valid) (right : state.right.Valid) :
    (rebalance state).1.size = state.size := by
  have sizes := (rebalance_spec state left right).2.1.size_eq
  simpa only [state_size] using sizes.symm

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
