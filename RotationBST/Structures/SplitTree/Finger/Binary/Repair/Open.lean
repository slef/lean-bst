module

public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Rotations

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Repairs retain the same bound with any enclosing larger-key remainder. -/
theorem repairOpen_rotations (t : Multiway) (restTree : Tree) :
    Rotations (openView t restTree) (openView (t.repairFirst).1 restTree) (repairOpenCost t) := by
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
        simp only [openView, repairOpenCost, repairFirst, prepareLeft, binaryView,
          List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | three c d e =>
        simp only [openView, repairOpenCost, repairFirst, prepareLeft, binaryView,
          List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | four c d e f =>
        simp only [openView, repairOpenCost, repairFirst, prepareLeft, binaryView,
          List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right (.step .right (.step (.inRight .left) .refl))).inRight.inRight
  | three first second rest =>
    cases first with
    | nil => exact .refl
    | three a b c => exact .refl
    | four a b c d => exact .refl
    | two a b =>
      cases second with
      | nil => exact .refl
      | two c d =>
        simp only [openView, repairOpenCost, repairFirst, binaryView,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | three c d e =>
        simp only [openView, repairOpenCost, repairFirst, binaryView,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | four c d e f =>
        simp only [openView, repairOpenCost, repairFirst, binaryView,
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
        simp only [openView, repairOpenCost, repairFirst, binaryView,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | three c d e =>
        simp only [openView, repairOpenCost, repairFirst, binaryView,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right Rotations.refl).inRight.inRight
      | four c d e f =>
        simp only [openView, repairOpenCost, repairFirst, binaryView,
          repairViewCost, List.append_assoc, comb_append, comb, binary]
        apply comb_rotations
        exact (Rotations.step Rotate.right (.step .right (.step (.inRight .left) .refl))).inRight.inRight

end RotationBST.Geometric.Split.Multiway.Finger
