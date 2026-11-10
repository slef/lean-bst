module

import RotationBST.Audit.Check
public import RotationBST.Classical.WeightBalanced.AbstractBridge

@[expose] public section

/-! Weight-balanced trees: the height bound of trees of bounded balance, and
rebuilding a tree into the balanced tree by at most `2n` rotations.
`Definitions/Abstract` gives `weight`, `Balanced`, `vineCost` and `rebuild`;
`Models/Rotation/Abstract` gives `Tree.balanced` and `Tree.height`. -/
namespace RotationBST.Classical.WeightBalanced.Results
open _root_.RotationBST.Tree (height balanced)
open Static

/-- **Height of trees of bounded balance.** If every child's weight is at most
`β` times its parent's, the height is at most `log_{1/β}(n + 1)`. -/
theorem height_le (β : ℝ) (hβ : 0 < β ∧ β < 1) (t : Tree) (h : Balanced β t) :
    (height t : ℝ) ≤ Real.logb (1 / β) (t.size + 1) :=
  WeightBalanced.height_le β hβ t h

/-- The balanced tree is `β`-balanced for every `β ≥ 2/3`. -/
theorem balanced_balanced (β : ℝ) (hβ : 2 / 3 ≤ β) (n : Nat) : Balanced β (balanced n) :=
  WeightBalanced.balanced_balanced β hβ n

/-- Rebuilding produces the balanced tree on the same keys… -/
theorem rebuild_tree (t : Tree) : (rebuild t).1 = balanced t.size := rfl

/-- …of minimum height… -/
theorem rebuild_height (t : Tree) (h : 0 < t.size) : height (rebuild t).1 = Nat.log2 t.size + 1 :=
  Static.balanced_height_eq t.size h

/-- …by exactly the reported number of rotations… -/
theorem rebuild_rotations (t : Tree) : Rotations t (rebuild t).1 (rebuild t).2 :=
  WeightBalanced.rebuild_rotations t

/-- …at most two per key. -/
theorem rebuild_cost (t : Tree) : (rebuild t).2 ≤ 2 * t.size :=
  WeightBalanced.rebuild_cost t

end RotationBST.Classical.WeightBalanced.Results

/-- info: abstract audit passed for `RotationBST.Classical.WeightBalanced.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.WeightBalanced.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Classical.WeightBalanced.Definitions.Abstract]
