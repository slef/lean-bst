module

public import RotationBST.Bounds.StaticTree.Abstract
public import RotationBST.Bounds.Implications.Proofs
public import RotationBST.Algorithms.Splay.WorkingSet.SplayBound
public import RotationBST.Algorithms.Splay.StaticOptimality

@[expose] public section

namespace RotationBST.Splay.Bridge

theorem staticOptimality_fixedTree (t u : Tree) (xs : List Nat) (same : t.size = u.size)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 12 * (StaticTree.cost u xs : ℝ) := by
  have h := Splay.staticOptimality_all_accessed t xs valid covers
  have hs := StaticTree.entropy_le_cost u xs (by rwa [← same])
  rw [← same] at hs
  linarith

end RotationBST.Splay.Bridge
