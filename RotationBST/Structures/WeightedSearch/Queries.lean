module

public import RotationBST.Structures.WeightedSearch.Regularization
public import RotationBST.Models.Pointer.Execution
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedSearch

/-- The biased depth bound is realized by an actual conventional pointer
search, including the return path and request unit. -/
theorem balanced_query (weights : List Nat) (x : Nat) (valid : x < weights.length)
    (positive : 0 < weights[x]) :
    ∃ k, Pointer.Serves (balancedBuild weights) (balancedBuild weights) x k ∧
      (k : ℝ) ≤ 1 + 2 * Real.logb 2 (3 * (weights.sum : ℝ) / weights[x]) ∧
      (k : ℝ) ≤ 1 + 2 * Real.logb 2 (2 * weights.length) := by
  have validTree : x < (balancedBuild weights).size := by simpa only [balanced_size] using valid
  have biased := balanced_depth_weighted weights x valid positive
  have uniform := balanced_depth_uniform weights x valid
  refine ⟨1 + 2 * Tree.depth (balancedBuild weights) x,
    Pointer.static_request _ x validTree, ?_, ?_⟩ <;> simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] <;> linarith

end RotationBST.WeightedSearch
