module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- First-child repair preserves the finger representation with at most three
local rotations, independently of the finger's length and attached subtree sizes. -/
theorem repairView_rotations (t : Multiway) :
    Rotations (binaryView t).tree (binaryView (repairView t).1).tree (repairView t).2 := by
  cases t with
  | nil => exact .refl
  | two first second =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d =>
        simp only [repairView, repairFirst, prepareLeft, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        exact .refl
      | three c d e =>
        simp only [repairView, repairFirst, prepareLeft, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        exact .refl
      | four c d e f =>
        simp only [repairView, repairFirst, prepareLeft, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
  | three first second rest =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | three c d e =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | four c d e f =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right (.step .right (.step (.inRight .left) .refl))).inRight.inRight
  | four first second third fourth =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | three c d e =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | four c d e f =>
        simp only [repairView, repairFirst, binaryView, BinaryView.tree,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right (.step .right (.step (.inRight .left) .refl))).inRight.inRight

end RotationBST.Arboral.Split.Multiway.Finger
