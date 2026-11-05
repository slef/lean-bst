module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Consequences.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Consequences.Results

/-- The unit-weight benchmark is exactly the normalized dynamic-finger sum. -/
theorem unit_weights (p : Nat) (xs : List Nat) :
    WeightedFinger.costFrom (fun _ => 1) p xs = Bounds.dynamicFingerCostFrom p xs :=
  unit_weight_cost p xs

/-- Dynamic finger with the same specified predecessor in both benchmarks. -/
theorem dynamic_finger_from (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCostFrom n p xs : ℝ) ≤ 4 * Bounds.dynamicFingerCostFrom p xs :=
  optimal_dynamic_finger_from n p xs hp valid

/-- The selected static tree starts at its root; the dynamic-finger benchmark
starts at `p`. The difference costs at most `n` once. -/
theorem dynamic_finger (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ n + 4 * Bounds.dynamicFingerCostFrom p xs :=
  optimal_dynamic_finger n p xs hp valid

theorem dynamic_finger_long (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (long : n ≤ xs.length) :
    (optimalCost n xs : ℝ) ≤ 5 * Bounds.dynamicFingerCostFrom p xs :=
  optimal_dynamic_finger_long n p xs hp valid long

/-- The best lazy-finger tree satisfies the static-optimality entropy bound. -/
theorem static_optimality (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ 2 * Bounds.staticCost n xs :=
  optimal_static_entropy n xs valid

/-- Uniform static-finger bound, including fingers outside the key universe. -/
theorem static_finger (n f : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) ≤ 6 * Bounds.fingerCost f xs :=
  optimal_static_finger n f xs valid

/-- The three consequences in §1.4 of arXiv:1304.6897 hold for one optimal
static tree. The choice can depend on the sequence, but precedes quantification
over the fixed finger and predecessor. This is not an online tree-selection rule. -/
theorem simultaneous (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t.size = n ∧ cost t xs = optimalCost n xs ∧
      (cost t xs : ℝ) ≤ 2 * Bounds.staticCost n xs ∧
      (∀ f, (cost t xs : ℝ) ≤ 6 * Bounds.fingerCost f xs) ∧
      ∀ p, p < n → (cost t xs : ℝ) ≤ n + 4 * Bounds.dynamicFingerCostFrom p xs :=
  optimal_three_bounds n xs valid

end RotationBST.LazyFinger.Consequences.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Consequences.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Consequences.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract,
  RotationBST.Bounds.DynamicFinger.Definitions.Abstract]
