module

public import RotationBST.Models.Rotation.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace RotationBST.Splay

/-- Positive analysis weights are indexed by implicit inorder rank. -/
def mass (w : Nat → ℝ) : Tree → Nat → ℝ
  | .nil, _ => 0
  | .node l r, lo => mass w l lo + w (lo + l.size) + mass w r (lo + l.size + 1)

/-- Sum of the binary logarithms of all nonempty subtree masses. -/
noncomputable def potential (w : Nat → ℝ) : Tree → Nat → ℝ
  | .nil, _ => 0
  | .node l r, lo => potential w l lo + potential w r (lo + l.size + 1) +
      Real.logb 2 (mass w (.node l r) lo)

end RotationBST.Splay
