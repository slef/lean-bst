module

public import RotationBST.Classical.RankBalanced.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RankBalanced
open Classical.RankBalanced

private def leaf : RankedTree := .node .nil 0 .nil
-- Three keys, ranks 1 / 0 0: AVL, red-black and WAVL.
private def three : RankedTree := .node leaf 1 leaf
-- A red-black tree with a 0-child (a red node) on the right.
private def redRight : RankedTree := .node leaf 1 (.node leaf 1 leaf)
-- A 2,2 node: WAVL but not AVL.
private def wide : RankedTree := .node leaf 2 leaf

example : Valid .avl three ∧ Valid .redBlack three ∧ Valid .wavl three := by
  simp [three, leaf, Valid, Rule.Local, NoZeroChild, rank]
example : Valid .redBlack redRight := by
  simp [redRight, leaf, Valid, Rule.Local, NoZeroChild, rank]
example : ¬ Valid .avl redRight := by
  simp [redRight, leaf, Valid, Rule.Local, rank]
example : Valid .wavl wide ∧ ¬ Valid .avl wide := by
  simp [wide, leaf, Valid, Rule.Local, rank]
-- A chain of two 0-children violates the red-black rule.
example : ¬ Valid .redBlack (.node .nil 0 (.node .nil 0 (.node .nil 0 .nil))) := by
  simp [Valid, Rule.Local, NoZeroChild, rank]

example : (Classical.Static.height redRight.erase : ℝ) ≤ 2 * Real.logb 2 (redRight.erase.size + 1) :=
  Results.redBlack_height redRight (by simp [redRight, leaf, Valid, Rule.Local, NoZeroChild, rank])
example (t : RankedTree) (h : Valid .avl t) :
    (Classical.Static.height t.erase : ℝ) ≤ 2 * Real.logb 2 (t.erase.size + 1) :=
  Results.wavl_height t (Results.avl_wavl t h)

end RotationBST.Tests.RankBalanced
