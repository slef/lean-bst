module

public import RotationBST.Classical.Static.Optimal.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.OptimalStatic
open _root_.RotationBST.Tree (balanced)
open Classical.Static Classical.Static.Optimal

private def w : List Nat := [5, 1, 9, 2]

-- The recurrence and Knuth's algorithm agree on a small instance; Knuth
-- examines fewer roots than the cubic recurrence would.
example : optCost w = 26 := by decide +kernel
example : knuth (rangeWeight w) 4 = (26, 15) := by decide +kernel
example : (optTree w).size = 4 := Results.optTree_size w
example : weightedCost w (optTree w) = 26 := by decide +kernel
-- Largest optimal roots: key 2 (weight 9) for the whole range; ties go right.
example : root (rangeWeight w) 0 4 = 2 := by decide +kernel
example : root (rangeWeight [1, 1]) 0 2 = 1 := by decide +kernel

-- The balanced tree is not optimal for skewed weights.
example : weightedCost w (balanced 4) = 30 := by decide +kernel
example : optCost w ≤ weightedCost w (balanced 4) :=
  Results.optCost_le w (balanced 4) (by decide +kernel)

-- Request counts give the static search cost.
example : counts 4 [2, 2, 0, 3, 2] = [1, 0, 3, 1] := by decide
example : StaticTree.cost (optTree (counts 4 [2, 2, 0, 3, 2])) [2, 2, 0, 3, 2] =
    optCost (counts 4 [2, 2, 0, 3, 2]) :=
  (Results.optTree_static 4 [2, 2, 0, 3, 2] (by decide)).2
example (t : Tree) (ht : t.size = 4) :
    optCost (counts 4 [2, 2, 0, 3, 2]) ≤ StaticTree.cost t [2, 2, 0, 3, 2] :=
  Results.optCost_le_static 4 _ t ht (by decide)

-- Knuth's bound on the steps, for any key weights.
example (v : List Nat) : (knuth (rangeWeight v) v.length).2 ≤ 2 * v.length ^ 2 :=
  Results.knuth_steps_le v

end RotationBST.Tests.OptimalStatic
