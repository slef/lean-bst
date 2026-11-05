module

public import RotationBST.Structures.WeightedSearch.Logarithms
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedSearch

@[simp] theorem regularize_length (weights : List Nat) : (regularize weights).length = weights.length := by
  simp [regularize]

theorem regularize_sum (weights : List Nat) : (regularize weights).sum = weights.length * (2 * weights.sum + 1) := by
  have affine (xs : List Nat) (a b : Nat) :
      (xs.map fun w => a * w + b).sum = a * xs.sum + b * xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  unfold regularize
  simp_rw [Nat.add_assoc]
  rw [affine]
  ring

theorem balanced_size (weights : List Nat) : (balancedBuild weights).size = weights.length := by
  rw [balancedBuild, build_size, regularize_length]

/-- The uniform part caps the depth of every key, even an unobserved key. -/
theorem balanced_capacity (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (balancedBuild weights) x ≤ 2 * weights.length := by
  have mass := build_mass (regularize weights) x (by simpa using valid)
  have index : x < (regularize weights).length := by simpa using valid
  have entry : (regularize weights)[x] = weights.length * weights[x] + weights.sum + 1 := by simp [regularize]
  rw [entry, regularize_sum] at mass
  change 2 ^ Tree.depth (balancedBuild weights) x *
    (weights.length * weights[x] + weights.sum + 1) ≤ weights.length * (2 * weights.sum + 1) at mass
  have smaller := Nat.mul_le_mul_left (2 ^ Tree.depth (balancedBuild weights) x)
    (show weights.sum + 1 ≤ weights.length * weights[x] + weights.sum + 1 by omega)
  have upper : weights.length * (2 * weights.sum + 1) ≤ (2 * weights.length) * (weights.sum + 1) := by nlinarith
  exact Nat.le_of_mul_le_mul_right (smaller.trans (mass.trans upper)) (by omega)

/-- The uniform baseline changes the frequency-biased depth bound by at most
a factor three inside the logarithm. Zero-frequency entries are also covered. -/
theorem balanced_mass (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (balancedBuild weights) x * weights[x] ≤ 3 * weights.sum := by
  by_cases zero : weights.sum = 0
  · have entry : weights[x] ≤ weights.sum := List.le_sum_of_mem (List.getElem_mem valid)
    have keyZero : weights[x] = 0 := by omega
    simp [keyZero]
  · have mass := build_mass (regularize weights) x (by simpa using valid)
    have index : x < (regularize weights).length := by simpa using valid
    have entry : (regularize weights)[x] = weights.length * weights[x] + weights.sum + 1 := by simp [regularize]
    rw [entry, regularize_sum] at mass
    change 2 ^ Tree.depth (balancedBuild weights) x *
      (weights.length * weights[x] + weights.sum + 1) ≤ weights.length * (2 * weights.sum + 1) at mass
    have positive : 0 < weights.length := by omega
    have scaled : weights.length * (2 ^ Tree.depth (balancedBuild weights) x * weights[x]) ≤
        weights.length * (3 * weights.sum) := by
      have smaller := Nat.mul_le_mul_left (2 ^ Tree.depth (balancedBuild weights) x)
        (show weights.length * weights[x] ≤ weights.length * weights[x] + weights.sum + 1 by omega)
      have upper := Nat.mul_le_mul_left weights.length (show 2 * weights.sum + 1 ≤ 3 * weights.sum by omega)
      calc
        _ = 2 ^ Tree.depth (balancedBuild weights) x * (weights.length * weights[x]) := by ring
        _ ≤ _ := smaller.trans (mass.trans upper)
    exact Nat.le_of_mul_le_mul_left scaled positive

theorem balanced_depth_uniform (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    (Tree.depth (balancedBuild weights) x : ℝ) ≤ Real.logb 2 (2 * weights.length) := by
  have capacity := balanced_capacity weights x valid
  have ratio : (2 : ℝ) ^ Tree.depth (balancedBuild weights) x ≤ 2 * weights.length := by exact_mod_cast capacity
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

theorem balanced_depth_weighted (weights : List Nat) (x : Nat) (valid : x < weights.length)
    (positive : 0 < weights[x]) :
    (Tree.depth (balancedBuild weights) x : ℝ) ≤ Real.logb 2 (3 * (weights.sum : ℝ) / weights[x]) := by
  have mass := balanced_mass weights x valid
  have weightPositive : (0 : ℝ) < weights[x] := by exact_mod_cast positive
  have ratio : (2 : ℝ) ^ Tree.depth (balancedBuild weights) x ≤ 3 * (weights.sum : ℝ) / weights[x] := by
    apply (le_div_iff₀ weightPositive).mpr
    exact_mod_cast mass
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

end RotationBST.WeightedSearch
