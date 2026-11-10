module

public import RotationBST.Classical.Static.Definitions.Abstract
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Weight balance (Nievergelt and Reingold's trees of bounded balance) and
rebuilding a subtree by rotations. The weight of a tree is its size plus one,
its number of empty leaves. -/
namespace RotationBST.Classical.WeightBalanced

/-- The number of empty leaves: size plus one. -/
def weight (t : Tree) : Nat := t.size + 1

/-- Every child's weight is at most `β` times its parent's. -/
def Balanced (β : ℝ) : Tree → Prop
  | .nil => True
  | .node l r =>
      (weight l : ℝ) ≤ β * weight (.node l r) ∧ (weight r : ℝ) ≤ β * weight (.node l r) ∧
        Balanced β l ∧ Balanced β r

/-- Rotations used to turn a tree into its right spine: the root's left
subtree is emptied one right rotation per node, then the rest of the spine. -/
def vineCost : Tree → Nat
  | .nil => 0
  | .node l r => l.size + vineCost r

/-- Rebuild a tree into the balanced tree on its keys: rotate to the right
spine, then run the same procedure for the balanced tree backwards. Returns
the new tree and the number of rotations. -/
def rebuild (t : Tree) : Tree × Nat :=
  (Static.balanced t.size, vineCost t + vineCost (Static.balanced t.size))

end RotationBST.Classical.WeightBalanced
