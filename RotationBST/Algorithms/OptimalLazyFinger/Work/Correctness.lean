module

public import RotationBST.Algorithms.OptimalLazyFinger.Work.DynamicProgram
public import RotationBST.Algorithms.OptimalLazyFinger.Correctness

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work

/-- The counted implementation constructs an optimal tree, with its entire
preprocessing and search over roots bounded in the annotated RAM model. -/
theorem tree_spec (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (tree n xs).ret.size = n ∧
      LazyFinger.cost (tree n xs).ret xs = LazyFinger.optimalCost n xs ∧
      (tree n xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := by
  refine ⟨?_, ?_, tree_time n xs⟩
  · rw [tree_ret]; exact OptimalLazyFinger.tree_size n xs
  · rw [tree_ret]; exact OptimalLazyFinger.tree_optimal n xs valid

theorem treeFrom_spec (n p : Nat) (xs : List Nat) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (treeFrom n p xs).ret.size = n ∧
      LazyFinger.costFrom (treeFrom n p xs).ret p xs = LazyFinger.optimalCostFrom n p xs ∧
      (treeFrom n p xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := by
  refine ⟨?_, ?_, treeFrom_time n p xs⟩
  · rw [treeFrom_ret]; exact OptimalLazyFinger.treeFrom_size n p xs
  · rw [treeFrom_ret]; exact OptimalLazyFinger.treeFrom_optimal n p xs hp valid

end RotationBST.OptimalLazyFinger.Work
