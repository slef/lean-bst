module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Repair.Results

/-- Repair preserves the concrete finger BST representation in at most three
rotations, as well as the multiway balance and node reserve. -/
theorem repair {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations (binaryView t).tree (binaryView (repairView t).1).tree (repairView t).2 ∧
      (repairView t).2 ≤ 3 ∧ (repairView t).1.nodes ≤ t.nodes ∧
      (Balanced h (repairView t).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (repairView t).1) :=
  ⟨repairView_rotations t, repairViewCost_bound t, repairFirst_nodes t, valid.repairFirst⟩

/-- The same local repair works before any larger-key remainder, with no
factor depending on spine length or the size of that remainder. -/
theorem before_remainder (t : Multiway) (rest : Tree) :
    Rotations (openView t rest) (openView (t.repairFirst).1 rest) (repairOpenCost t) ∧
      repairOpenCost t ≤ 3 := ⟨repairOpen_rotations t rest, repairOpenCost_bound t⟩

end RotationBST.Arboral.Split.Multiway.Finger.Repair.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Finger.Repair.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Repair.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs]
