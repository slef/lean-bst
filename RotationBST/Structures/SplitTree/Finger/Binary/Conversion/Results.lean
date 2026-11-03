module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.Conversion.Results

/-- Construct the minimum-finger BST in at most three rotations per level. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (binaryView t).tree (conversionCost t) ∧ conversionCost t ≤ 3 * h :=
  ⟨conversion_rotations t, conversion_cost valid⟩

/-- Conversion also works before an arbitrary enclosing remainder. -/
theorem before_remainder {h : Nat} {t : Multiway} (valid : Balanced h t) (rest : Tree) :
    Rotations (.node t.binary rest) (openView t rest) (openConversionCost t) ∧
      openConversionCost t ≤ 3 * h := ⟨openConversion_rotations t rest, openConversion_cost valid⟩

end RotationBST.Geometric.Split.Multiway.Finger.Conversion.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Finger.Conversion.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Finger.Conversion.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs]
