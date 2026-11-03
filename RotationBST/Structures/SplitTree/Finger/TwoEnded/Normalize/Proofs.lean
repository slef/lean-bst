module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Proofs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Rebalance

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

theorem normalize_spec (fragment : Fragment) (valid : fragment.Valid) :
    IntervalValid (normalize fragment).1 ∧
      Rotations fragment.tree (intervalTree (normalize fragment).1) (normalize fragment).2 := by
  cases fragment with
  | minimum p =>
    by_cases empty : p.tree = .nil
    · simp only [normalize, empty, ite_true, IntervalValid, Fragment.tree, intervalTree, binaryView, BinaryView.tree, comb]
      exact ⟨trivial, .refl⟩
    · simp only [normalize, empty, ite_false, IntervalValid, Fragment.tree, intervalTree]
      exact ⟨fromRoot_valid valid, (conversion_rotations p.tree).symm.append (fromRoot_rotations p.height p.tree empty)⟩
  | maximum p =>
    by_cases empty : p.tree = .nil
    · simp only [normalize, empty, ite_true, IntervalValid, Fragment.tree, intervalTree, maximumView, MaximumView.tree, leftComb]
      exact ⟨trivial, .refl⟩
    · simp only [normalize, empty, ite_false, IntervalValid, Fragment.tree, intervalTree]
      exact ⟨fromRoot_valid valid, (maximum_rotations p.tree).symm.append (fromRoot_rotations p.height p.tree empty)⟩
  | shared state => exact ⟨(rebalance_spec state valid.1 valid.2).1, (rebalance_spec state valid.1 valid.2).2.1⟩

theorem normalize_minimum_cost (p : Multiway.Partition.Piece) (valid : p.Valid) :
    (normalize (.minimum p)).2 ≤ 9 * p.height := by
  have initial := conversion_cost valid
  have establish := fromRoot_cost valid
  simp only [normalize]
  split <;> simp only <;> omega

theorem normalize_maximum_cost (p : Multiway.Partition.Piece) (valid : p.Valid) :
    (normalize (.maximum p)).2 ≤ 9 * p.height := by
  have initial := maximum_cost valid
  have establish := fromRoot_cost valid
  simp only [normalize]
  split <;> simp only <;> omega

theorem split_valid {state : State} (valid : state.HeightValid) (rank : Nat)
    (existsKey : rank < state.size) : IntervalValid (split state rank).left ∧ IntervalValid (split state rank).right := by
  have pieces := expose_valid state valid.1 valid.2.1 rank existsKey
  exact ⟨(normalize_spec _ pieces.1).1, (normalize_spec _ pieces.2).1⟩

theorem split_access {state : State} (valid : state.HeightValid) (rank : Nat)
    (existsKey : rank < state.size) : Access state.tree (split state rank).tree rank (split state rank).cost := by
  have exposed := expose_access state valid.1 valid.2.1 rank existsKey
  have pieces := expose_valid state valid.1 valid.2.1 rank existsKey
  have left := (normalize_spec _ pieces.1).2
  have right := (normalize_spec _ pieces.2).2
  constructor
  · exact (exposed.1.append left.inLeft).append right.inRight
  · exact left.size_eq.symm.trans exposed.2

theorem split_sizes {state : State} (valid : state.HeightValid) (rank : Nat)
    (existsKey : rank < state.size) :
    (intervalTree (split state rank).left).size = rank ∧
      (intervalTree (split state rank).right).size = state.size - 1 - rank := by
  have access := split_access valid rank existsKey
  have first := access.2
  have sizes := access.1.size_eq
  simp only [SplitResult.tree, Tree.size, state_size] at sizes
  change (intervalTree (split state rank).left).size = rank at first
  exact ⟨first, by omega⟩

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
