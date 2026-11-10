module

public import RotationBST.Classical.WeightBalanced.Abstract
public import RotationBST.Models.Rotation.Shapes
public import RotationBST.Classical.Static.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.WeightBalanced
open _root_.RotationBST.Tree (height balanced)
open Classical.Static Classical.WeightBalanced

private def path : Nat → Tree
  | 0 => .nil
  | n + 1 => .node .nil (path n)
private def leftPath : Nat → Tree
  | 0 => .nil
  | n + 1 => .node (leftPath n) .nil

-- A right path is already a spine; a left path needs one rotation per edge.
example : vineCost (path 6) = 0 ∧ vineCost (leftPath 6) = 5 := by decide

-- Rebuilding a left path on 7 keys reaches the balanced tree in at most 14
-- rotations (6 to the spine, then 4 back to the perfect tree).
example : Rotations (leftPath 7) (balanced 7) (rebuild (leftPath 7)).2 :=
  Results.rebuild_rotations (leftPath 7)
example : (rebuild (leftPath 7)).2 ≤ 14 := Results.rebuild_cost (leftPath 7)
example : height (rebuild (leftPath 7)).1 = Nat.log2 7 + 1 :=
  Results.rebuild_height (leftPath 7) (by decide)

-- The balanced tree is 2/3-balanced, hence of height at most log_{3/2}(n + 1).
example (n : Nat) : (height (balanced n) : ℝ) ≤ Real.logb (1 / (2 / 3)) (n + 1) := by
  have := Results.height_le (2 / 3) (by norm_num) (balanced n)
    (Results.balanced_balanced (2 / 3) le_rfl n)
  simpa [Tree.balanced_size] using this

-- No tree on 1000 keys is lower than the balanced one.
example (t : Tree) (h : t.size = 1000) : height (balanced 1000) ≤ height t := by
  rw [Classical.Static.Results.balanced_height_eq 1000 (by decide)]
  have := Classical.Static.Results.log2_add_one_le_height t (by omega)
  rwa [h] at this

end RotationBST.Tests.WeightBalanced
