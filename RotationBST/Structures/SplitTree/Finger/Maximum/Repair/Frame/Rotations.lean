module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

theorem maximumFrame_closed_grouping (h : Nat) (frame : Frame) (right : IsRightFrame frame) :
    Rotations (maximumFrameRemainder frame none) (maximumFrameSibling h frame).tree.binary
      (maximumFrameClosedCost frame) := by
  cases frame <;> simp only [IsRightFrame] at right
  · exact .refl
  · exact .refl
  · exact .step .right .refl

theorem maximumRepairFrame_rotations (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (right : IsRightFrame frame) :
    Rotations (maximumOpenView focus (maximumFrameRemainder frame none))
      (maximumView (maximumRepairFrame expected actual focus frame).tree).tree
      (maximumRepairFrame expected actual focus frame).cost :=
  (maximumOpenView_tail_rotations focus (maximumFrame_closed_grouping expected frame right)).append
    (attachLeft_rotations actual (maximumFrameSibling expected frame).height focus (maximumFrameSibling expected frame).tree)

theorem maximumFrame_grouping (h : Nat) (frame : Frame) (right : IsRightFrame frame) (rest : Tree) :
    Rotations (maximumFrameRemainder frame (some rest)) (.node rest (maximumFrameSibling h frame).tree.binary)
      (maximumFrameGroupingCost frame) := by
  cases frame <;> simp only [IsRightFrame] at right
  · exact .refl
  · exact .step .right .refl
  · exact .step .right (.step .right .refl)

theorem maximumRepairFrame_open (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (right : IsRightFrame frame) (rest : Tree) :
    Rotations (maximumOpenView focus (maximumFrameRemainder frame (some rest)))
      (maximumOpenView (maximumRepairFrame expected actual focus frame).tree rest)
      (maximumRepairFrameOpenCost expected actual focus frame) :=
  (maximumOpenView_tail_rotations focus (maximumFrame_grouping expected frame right rest)).append
    (attachLeft_open actual (maximumFrameSibling expected frame).height focus (maximumFrameSibling expected frame).tree rest)

end RotationBST.SplitTree.Multiway.Finger
