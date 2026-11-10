module

import RotationBST.Audit.Check
public import RotationBST.Classical.RankBalanced.AbstractBridge

@[expose] public section

/-! Rank-balanced trees: heights and ranks under the AVL, red-black and WAVL
rules. `Definitions/Abstract` gives ranked trees and the rules; heights count
nodes (`Static.height`) and sizes are those of the underlying shape. -/
namespace RotationBST.Classical.RankBalanced.Results
open Static

/-- In an AVL tree a node's rank is its height in edges. -/
theorem avl_height_rank (t : RankedTree) (h : Valid .avl t) : (height t.erase : Int) = rank t + 1 :=
  RankBalanced.avl_height_rank t h

/-- **AVL trees** have height at most `log_φ(n + 1)`, about `1.44 log₂ n`. -/
theorem avl_height (t : RankedTree) (h : Valid .avl t) :
    (height t.erase : ℝ) ≤ Real.logb Real.goldenRatio (t.erase.size + 1) :=
  RankBalanced.avl_height t h

/-- **Red-black trees** have height at most `2 log₂(n + 1)`. -/
theorem redBlack_height (t : RankedTree) (h : Valid .redBlack t) :
    (height t.erase : ℝ) ≤ 2 * Real.logb 2 (t.erase.size + 1) :=
  RankBalanced.redBlack_height t h

/-- **WAVL trees** have rank (hence height) at most `2 log₂(n + 1)`. -/
theorem wavl_rank (t : RankedTree) (h : Valid .wavl t) :
    (rank t : ℝ) + 1 ≤ 2 * Real.logb 2 (t.erase.size + 1) :=
  RankBalanced.wavl_rank t h

theorem wavl_height (t : RankedTree) (h : Valid .wavl t) :
    (height t.erase : ℝ) ≤ 2 * Real.logb 2 (t.erase.size + 1) :=
  RankBalanced.wavl_height t h

/-- Every AVL tree is a WAVL tree. -/
theorem avl_wavl (t : RankedTree) (h : Valid .avl t) : Valid .wavl t :=
  RankBalanced.avl_wavl t h

end RotationBST.Classical.RankBalanced.Results

/-- info: abstract audit passed for `RotationBST.Classical.RankBalanced.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.RankBalanced.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Classical.Static.Definitions.Abstract,
  RotationBST.Classical.RankBalanced.Definitions.Abstract]
