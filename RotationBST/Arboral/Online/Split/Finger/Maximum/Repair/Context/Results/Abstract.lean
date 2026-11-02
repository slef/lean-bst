module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Proofs

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
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract]
