module

import RotationBST.Audit.Check
public import RotationBST.Structures.WeightedSearch.AbstractBridge

@[expose] public section
namespace RotationBST.WeightedSearch.Results

/-- Weighted-median selection leaves at most half of the mass in either child. -/
theorem median (weights : List Nat) (nonempty : weights ≠ []) :
    pivot weights < weights.length ∧
      2 * (weights.take (pivot weights)).sum ≤ weights.sum ∧
      2 * (weights.drop (pivot weights + 1)).sum ≤ weights.sum :=
  ⟨pivot_lt weights nonempty, pivot_halves weights⟩

/-- All keys remain in their original inorder ranks, including zero weights. -/
theorem size (weights : List Nat) : (build weights).size = weights.length := build_size weights

/-- Exact integer form of the weighted search guarantee. -/
theorem mass (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (build weights) x * weights[x] ≤ weights.sum := build_mass weights x valid

theorem depth (weights : List Nat) (x : Nat) (valid : x < weights.length) (positive : 0 < weights[x]) :
    (Tree.depth (build weights) x : ℝ) ≤ Real.logb 2 ((weights.sum : ℝ) / weights[x]) :=
  build_depth weights x valid positive

/-- Adding a uniform baseline preserves the size of the represented universe. -/
theorem balanced_size (weights : List Nat) : (balancedBuild weights).size = weights.length :=
  WeightedSearch.balanced_size weights

/-- Every key in the regularized tree has logarithmic worst-case depth. -/
theorem balanced_capacity (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (balancedBuild weights) x ≤ 2 * weights.length :=
  WeightedSearch.balanced_capacity weights x valid

/-- The frequency-biased guarantee is retained within factor three in mass. -/
theorem balanced_mass (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (balancedBuild weights) x * weights[x] ≤ 3 * weights.sum :=
  WeightedSearch.balanced_mass weights x valid

/-- One tree simultaneously gives biased depth for positive-frequency keys and
uniform logarithmic depth, with zero-frequency keys retained. -/
theorem balanced_depth (weights : List Nat) (x : Nat) (valid : x < weights.length)
    (positive : 0 < weights[x]) :
    (Tree.depth (balancedBuild weights) x : ℝ) ≤ Real.logb 2 (3 * (weights.sum : ℝ) / weights[x]) ∧
      (Tree.depth (balancedBuild weights) x : ℝ) ≤ Real.logb 2 (2 * weights.length) :=
  ⟨balanced_depth_weighted weights x valid positive, balanced_depth_uniform weights x valid⟩

/-- Physical pointer searches realize both bounds, charging the outward path,
return path, and request unit. This is a query guarantee, not a preprocessing
runtime theorem. -/
theorem query (weights : List Nat) (x : Nat) (valid : x < weights.length) (positive : 0 < weights[x]) :
    ∃ k, Pointer.Serves (balancedBuild weights) (balancedBuild weights) x k ∧
      (k : ℝ) ≤ 1 + 2 * Real.logb 2 (3 * (weights.sum : ℝ) / weights[x]) ∧
      (k : ℝ) ≤ 1 + 2 * Real.logb 2 (2 * weights.length) := balanced_query weights x valid positive

end RotationBST.WeightedSearch.Results

/-- info: abstract audit passed for `RotationBST.WeightedSearch.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.WeightedSearch.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.WeightedSearch.Definitions.Abstract]
