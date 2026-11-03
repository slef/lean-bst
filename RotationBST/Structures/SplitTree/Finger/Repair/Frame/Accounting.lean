module

public import RotationBST.Structures.SplitTree.Finger.Repair.Frame.Balance
public import RotationBST.Structures.SplitTree.Multiway.Join.Nodes

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

theorem attachRight_nodes (hl hr : Nat) (l r : Multiway) :
    (attachRight hl hr l r).tree.nodes ≤ l.nodes + r.nodes + (hr - hl) + 1 := by
  have bound := Multiway.Join.joinLeft_nodes (hr - hl) l r
  have root := Multiway.Join.promotion_tree_nodes (Multiway.Join.joinLeft (hr - hl) l r).1
  simp only [attachRight, Multiway.Join.finish_tree]
  omega

theorem repairFrame_nodes (expected actual : Nat) (focus : Multiway) (frame : Frame)
    (left : IsLeftFrame frame) :
    (repairFrame expected actual focus frame).tree.nodes ≤
      (frame.fill focus).nodes + (expected + 1 - actual) + 1 := by
  have bound := attachRight_nodes actual (frameSibling expected frame).height focus (frameSibling expected frame).tree
  cases frame <;> simp only [IsLeftFrame] at left
  all_goals simp only [repairFrame, frameSibling, Frame.fill, nodes] at *; omega

/-- If a one-level deficit propagates, exactly one enclosing node disappears
and the finger rotations cost at most two. That node pays for this step. -/
theorem repairFrame_merge {h : Nat} (focus : Multiway) {frame : Frame}
    (siblings : frame.Valid (h + 1)) (left : IsLeftFrame frame)
    (continues : (repairFrame (h + 1) h focus frame).height = h + 1) :
    (repairFrame (h + 1) h focus frame).tree.nodes + 1 = (frame.fill focus).nodes ∧
      (repairFrame (h + 1) h focus frame).cost ≤ 2 ∧
      repairFrameOpenCost (h + 1) h focus frame ≤ 2 := by
  cases frame <;> simp only [IsLeftFrame] at left
  case twoLeft b =>
    change Balanced (h + 1) b at siblings
    cases siblings with
    | two ha hb =>
      simp [repairFrame, frameSibling, attachRight, Multiway.Join.joinLeft, Multiway.Join.finish,
        repairFrameOpenCost, frameGroupingCost, joinOpenCost, joinViewCost, Frame.fill, nodes]
      omega
    | three ha hb hc =>
      simp [repairFrame, frameSibling, attachRight, Multiway.Join.joinLeft, Multiway.Join.finish,
        repairFrameOpenCost, frameGroupingCost, joinOpenCost, joinViewCost, Frame.fill, nodes]
      omega
    | four ha hb hc hd =>
      simp [repairFrame, frameSibling, attachRight, Multiway.Join.joinLeft, Multiway.Join.finish] at continues
  case threeFirst b c =>
    have height := attachRight_taller_two (show h < h + 1 + 1 by omega) focus b c
    change (attachRight h (h + 1 + 1) focus (.two b c)).height = h + 1 at continues
    omega
  case fourFirst b c d =>
    have height := attachRight_taller_three (show h < h + 1 + 1 by omega) focus b c d
    change (attachRight h (h + 1 + 1) focus (.three b c d)).height = h + 1 at continues
    omega

end RotationBST.Arboral.Split.Multiway.Finger
