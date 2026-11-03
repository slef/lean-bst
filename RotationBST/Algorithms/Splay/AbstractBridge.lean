module

public import RotationBST.Algorithms.Splay.Pointer
public import RotationBST.Algorithms.Splay.WorkingSet.SplayBound
public import RotationBST.Bounds.Normalization.AbstractBridge

@[expose] public section

namespace RotationBST.Splay.Bridge

theorem pointer_execution (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ∃ k, k ≤ 3 * algorithm.totalCost t xs ∧
      Pointer.Execution t xs (algorithm.runFrom [] t xs).1 k := by
  obtain ⟨k, hk, ht⟩ := runFrom_pointer [] t xs valid
  refine ⟨k, ?_, ht⟩
  unfold Algorithm.totalCost Algorithm.cost
  omega

theorem pointer_workingSet (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ∃ k, k ≤ 31 * workingSetSum t.size [] xs + 18 * t.size * (1 + t.size.log2) ∧
      Pointer.Execution t xs (algorithm.runFrom [] t xs).1 k := by
  obtain ⟨k, hk, ht⟩ := runFrom_pointer [] t xs valid
  have hb := workingSet_bound t xs valid
  have hl := BoundsBridge.length_le_workingSetSum t.size [] xs
  refine ⟨k, ?_, ht⟩
  unfold Algorithm.cost at hb
  simp only [Nat.mul_assoc] at hb ⊢
  omega

end RotationBST.Splay.Bridge
