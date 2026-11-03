module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Ends

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.Results

/-- The minimum finger reconstructs the original tree with one frame per level. -/
theorem representation {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Context.plug (leftSpine t) .nil = t ∧ Context.Valid 0 (leftSpine t) ∧ (leftSpine t).length = h :=
  ⟨leftSpine_plug t, leftSpine_balanced valid⟩

/-- Ascent reaches an ancestor interval containing the requested rank. -/
theorem contains (t : Multiway) (rank : Nat) (valid : rank < t.size) :
    rank < (Context.plug ((leftSpine t).take (searchLevels t rank)) .nil).size :=
  searchLevels_contains t rank valid

/-- Ascending from the nearer endpoint costs logarithmically many multiway
levels in the smaller side. BST realization and split rebalancing are separate. -/
theorem nearer_endpoint {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    nearSearchLevels t rank ≤ Nat.log2 (min rank (t.size - 1 - rank) + 1) + 1 :=
  nearSearchLevels_log valid rank

end RotationBST.SplitTree.Multiway.Finger.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Finger.Abstract]
