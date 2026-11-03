module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Endpoint

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Maximum.Results

/-- Construct the maximum-finger view while retaining all off-path subtrees,
in at most three rotations per multiway level. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (maximumView t).tree (maximumCost t) ∧ maximumCost t ≤ 3 * h :=
  ⟨maximum_rotations t, maximum_cost valid⟩

theorem endpoint (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (maximumView t).tree (t.size - 1) (maximumCost t) := maximumView_maximum t nonempty

end RotationBST.Arboral.Split.Multiway.Finger.Maximum.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Finger.Maximum.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs]
