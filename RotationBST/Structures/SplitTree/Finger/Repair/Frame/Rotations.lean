module

public import RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Join.Balance

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

theorem repairFrame_rotations (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (left : IsLeftFrame frame) :
    Rotations (openView focus (frameRemainder frame none))
      (binaryView (repairFrame expected actual focus frame).tree).tree
      (repairFrame expected actual focus frame).cost := by
  have result := attachRight_rotations actual (frameSibling expected frame).height focus (frameSibling expected frame).tree
  cases frame <;> simp only [IsLeftFrame] at left
  all_goals simpa only [repairFrame, frameSibling, frameRemainder, binary] using result

theorem frame_grouping (h : Nat) (frame : Frame) (left : IsLeftFrame frame) (rest : Tree) :
    Rotations (frameRemainder frame (some rest)) (.node (frameSibling h frame).tree.binary rest)
      (frameGroupingCost frame) := by
  cases frame <;> simp only [IsLeftFrame] at left
  · exact .refl
  · exact .step .left .refl
  · exact .step (.inRight .left) (.step .left .refl)

theorem repairFrame_open (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (left : IsLeftFrame frame) (rest : Tree) :
    Rotations (openView focus (frameRemainder frame (some rest)))
      (openView (repairFrame expected actual focus frame).tree rest)
      (repairFrameOpenCost expected actual focus frame) :=
  (openView_tail_rotations focus (frame_grouping expected frame left rest)).append
    (attachRight_open actual (frameSibling expected frame).height focus (frameSibling expected frame).tree rest)

end RotationBST.SplitTree.Multiway.Finger
