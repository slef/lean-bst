module

public import RotationBST.Bounds.Implications
public import RotationBST.WorkingSet.SplayBound
public import RotationBST.Splay.StaticOptimality

@[expose] public section

namespace RotationBST.Splay.Bridge

theorem staticFinger_all_accessed (t : Tree) (xs : List Nat) (f : Nat)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 12 * Bounds.fingerCost f xs := by
  have hs := Splay.staticOptimality_all_accessed t xs valid covers
  have hf := Bounds.static_le_finger t.size f xs valid
  linarith

end RotationBST.Splay.Bridge
