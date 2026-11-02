module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Endpoint

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

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract]
