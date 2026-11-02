module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Conversion.Results

/-- Construct the minimum-finger BST in at most three rotations per level. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (binaryView t).tree (conversionCost t) ∧ conversionCost t ≤ 3 * h :=
  ⟨conversion_rotations t, conversion_cost valid⟩

/-- Conversion also works before an arbitrary enclosing remainder. -/
theorem before_remainder {h : Nat} {t : Multiway} (valid : Balanced h t) (rest : Tree) :
    Rotations (.node t.binary rest) (openView t rest) (openConversionCost t) ∧
      openConversionCost t ≤ 3 * h := ⟨openConversion_rotations t rest, openConversion_cost valid⟩

end RotationBST.Arboral.Split.Multiway.Finger.Conversion.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Conversion.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract]
