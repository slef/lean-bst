module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Rebalance

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Height.Results

/-- Establish both endpoint views around the existing root, with adjacent side
heights, using at most six rotations per multiway level. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    (fromRoot h t).1.HeightValid ∧ Rotations t.binary (fromRoot h t).1.tree (fromRoot h t).2 ∧
      (fromRoot h t).2 ≤ 6 * h :=
  ⟨fromRoot_valid valid, fromRoot_rotations h t nonempty, fromRoot_cost valid⟩

/-- Height balance gives the needed logarithmic comparison with the nearer end,
even when the two side sizes differ by much more than a constant factor. -/
theorem endpoint_choice {state : State} (valid : state.HeightValid) (rank : Nat)
    (existsKey : rank < state.size) :
    Nat.log2 (chosenDistance state rank + 1) ≤
      2 * Nat.log2 (min rank (state.size - 1 - rank) + 1) + 2 :=
  chosenDistance_log valid rank existsKey

/-- Restore adjacent side heights, keeping all keys and both endpoint views.
The cost of triggering this rebuild still needs to be included in split accounting. -/
theorem restore (state : State) (left : state.left.Valid) (right : state.right.Valid) :
    (rebalance state).1.HeightValid ∧ Rotations state.tree (rebalance state).1.tree (rebalance state).2 ∧
      (rebalance state).1.size = state.size ∧
      (rebalance state).2 ≤ 12 * max state.left.height state.right.height + 6 :=
  ⟨(rebalance_spec state left right).1, (rebalance_spec state left right).2.1,
    rebalance_size state left right, (rebalance_spec state left right).2.2⟩

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Height.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Height.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Abstract]
