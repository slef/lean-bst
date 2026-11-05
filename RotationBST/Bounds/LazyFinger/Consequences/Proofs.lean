module

public import RotationBST.Bounds.LazyFinger.Abstract
public import RotationBST.Bounds.StaticTree.Construction
public import RotationBST.Bounds.Implications.StaticFinger
public import RotationBST.Bounds.WeightedFinger.Abstract
public import RotationBST.Bounds.DynamicFinger.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Unit weights give the ordinary consecutive-rank benchmark exactly. -/
theorem unit_weight_cost (p : Nat) (xs : List Nat) :
    WeightedFinger.costFrom (fun _ => 1) p xs = Bounds.dynamicFingerCostFrom p xs := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [WeightedFinger.costFrom, WeightedFinger.Results.unit_weights,
      Bounds.dynamicFingerCostFrom, Nat.dist_eq_max_sub_min, ih]

theorem optimal_dynamic_finger_from (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCostFrom n p xs : ℝ) ≤ 4 * Bounds.dynamicFingerCostFrom p xs := by
  have weights := WeightedFinger.Results.optimal_le (fun _ => 1) n p xs (by intros; norm_num) hp valid
  rw [unit_weight_cost] at weights
  have bound := (Results.characterization_from n p xs hp valid).2
  linarith

/-- Root initialization is charged once when the benchmark instead starts at
an externally specified predecessor. -/
theorem optimal_dynamic_finger (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ n + 4 * Bounds.dynamicFingerCostFrom p xs := by
  have start := (optimal_initialization_bounds n p xs hp valid).2
  have start' : (optimalCost n xs : ℝ) ≤ n + (optimalCostFrom n p xs : ℝ) := by exact_mod_cast start
  have bound := optimal_dynamic_finger_from n p xs hp valid
  linarith

theorem optimal_static_entropy (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ 2 * Bounds.staticCost n xs := by
  obtain ⟨t, size, entropy⟩ := StaticTree.entropy_tree n xs valid
  have compare := optimalCost_le_twice_static t xs
  rw [size] at compare
  have compare' : (optimalCost n xs : ℝ) ≤ 2 * (StaticTree.cost t xs : ℝ) := by exact_mod_cast compare
  linarith

theorem optimal_static_finger (n f : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ 6 * Bounds.fingerCost f xs := by
  have entropy := optimal_static_entropy n xs valid
  have finger := Bounds.static_le_finger n f xs valid
  linarith

/-- A long sequence absorbs the predecessor-to-root startup cost. -/
theorem optimal_dynamic_finger_long (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (long : n ≤ xs.length) :
    (optimalCost n xs : ℝ) ≤ 5 * Bounds.dynamicFingerCostFrom p xs := by
  have weights := WeightedFinger.Results.optimal_le (fun _ => 1) n p xs (by intros; norm_num) hp valid
  rw [unit_weight_cost] at weights
  have bound := (Results.characterization_long_sequence n p xs hp valid long).2
  linarith

/-- One optimal tree satisfies all three bounds, uniformly over the fixed
finger and the initial predecessor. Its choice may use the whole sequence. -/
theorem optimal_three_bounds (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t.size = n ∧ cost t xs = optimalCost n xs ∧
      (cost t xs : ℝ) ≤ 2 * Bounds.staticCost n xs ∧
      (∀ f, (cost t xs : ℝ) ≤ 6 * Bounds.fingerCost f xs) ∧
      ∀ p, p < n → (cost t xs : ℝ) ≤ n + 4 * Bounds.dynamicFingerCostFrom p xs := by
  obtain ⟨t, size, optimal⟩ := optimalCost_attained n xs
  refine ⟨t, size, optimal, ?_⟩
  rw [optimal]
  exact ⟨optimal_static_entropy n xs valid, fun f => optimal_static_finger n f xs valid,
    fun p hp => optimal_dynamic_finger n p xs hp valid⟩

end RotationBST.LazyFinger
