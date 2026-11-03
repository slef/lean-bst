module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Balance
public import RotationBST.Structures.SplitTree.Multiway.Join.Nodes

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem attachLeft_nodes (hl hr : Nat) (l r : Multiway) :
    (attachLeft hl hr l r).tree.nodes ≤ l.nodes + r.nodes + (hr - hl) + 1 := by
  have bound := Multiway.Join.joinRight_nodes (hr - hl) r l
  have root := Multiway.Join.promotion_tree_nodes (Multiway.Join.joinRight (hr - hl) r l).1
  simp only [attachLeft, Multiway.Join.finish_tree]
  omega

theorem maximumRepairFrame_nodes (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (left : IsRightFrame frame) :
    (maximumRepairFrame expected actual focus frame).tree.nodes ≤
      (frame.fill focus).nodes + (expected + 1 - actual) + 1 := by
  have bound := attachLeft_nodes actual (maximumFrameSibling expected frame).height focus (maximumFrameSibling expected frame).tree
  cases frame <;> simp only [IsRightFrame] at left
  all_goals simp only [maximumRepairFrame, maximumFrameSibling, Frame.fill, nodes] at *; omega

/-- If a one-level deficit propagates, exactly one enclosing node disappears
and the finger rotations cost at most two. That node pays for this step. -/
theorem maximumRepairFrame_merge {h : Nat} (focus : Multiway) {frame : Frame}
    (siblings : frame.Valid (h + 1)) (left : IsRightFrame frame)
    (continues : (maximumRepairFrame (h + 1) h focus frame).height = h + 1) :
    (maximumRepairFrame (h + 1) h focus frame).tree.nodes + 1 = (frame.fill focus).nodes ∧
      (maximumRepairFrame (h + 1) h focus frame).cost ≤ 2 ∧
      maximumRepairFrameOpenCost (h + 1) h focus frame ≤ 2 := by
  cases frame <;> simp only [IsRightFrame] at left
  case twoRight b =>
    change Balanced (h + 1) b at siblings
    cases siblings with
    | two ha hb =>
      simp [maximumRepairFrame, maximumFrameSibling, attachLeft, Multiway.Join.joinRight, Multiway.Join.finish,
        maximumRepairFrameOpenCost, maximumFrameGroupingCost, maximumJoinOpenCost, maximumJoinViewCost, maximumFrameClosedCost, Frame.fill, nodes]
      omega
    | three ha hb hc =>
      simp [maximumRepairFrame, maximumFrameSibling, attachLeft, Multiway.Join.joinRight, Multiway.Join.finish,
        maximumRepairFrameOpenCost, maximumFrameGroupingCost, maximumJoinOpenCost, maximumJoinViewCost, maximumFrameClosedCost, Frame.fill, nodes]
      omega
    | four ha hb hc hd =>
      simp [maximumRepairFrame, maximumFrameSibling, attachLeft, Multiway.Join.joinRight, Multiway.Join.finish] at continues
  case threeLast b c =>
    have height := attachLeft_taller_two (show h < h + 1 + 1 by omega) focus b c
    change (attachLeft h (h + 1 + 1) focus (.two b c)).height = h + 1 at continues
    omega
  case fourLast b c d =>
    have height := attachLeft_taller_three (show h < h + 1 + 1 by omega) focus b c d
    change (attachLeft h (h + 1 + 1) focus (.three b c d)).height = h + 1 at continues
    omega

end RotationBST.Arboral.Split.Multiway.Finger
