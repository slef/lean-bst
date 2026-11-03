module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Maximum.Repair.Results

/-- Repair a shortened last-child interval directly in its existing maximum
finger view. All rotations are counted; the repaired tree is balanced. -/
theorem repair (fs : List Context.Frame) {expected actual : Nat} {focus : Multiway}
    (balanced : Balanced actual focus) (ancestors : Context.Valid expected fs)
    (right : ∀ f ∈ fs, IsRightFrame f) (shorter : actual ≤ expected) :
    let result := maximumRepairContext expected actual focus fs
    Balanced result.height result.tree ∧ result.height ≤ expected + fs.length ∧
      Rotations (maximumEnclosingView focus fs) (maximumView result.tree).tree result.cost :=
  ⟨(maximumRepairContext_balance fs balanced ancestors right shorter).1,
    (maximumRepairContext_balance fs balanced ancestors right shorter).2,
    maximumRepairContext_rotations fs expected actual focus right⟩

end RotationBST.Arboral.Split.Multiway.Finger.Maximum.Repair.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Repair.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Context.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs]
