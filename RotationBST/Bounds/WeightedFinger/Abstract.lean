module

import RotationBST.Audit.Check
public import RotationBST.Bounds.WeightedFinger.AbstractBridge

@[expose] public section
namespace RotationBST.WeightedFinger.Results

/-- Unit weights specialize weighted dynamic finger to dynamic finger. This
identity alone does not assert a bound for GreedyASS. -/
theorem unit_weights (x y : Nat) :
    charge (fun _ => 1) x y = 1 + Real.logb 2 ((max x y - min x y + 1 : Nat) : ℝ) :=
  charge_unit x y

theorem repeated_key (w : Nat → ℝ) (x : Nat) (hx : 0 < w x) : charge w x x = 1 :=
  charge_self w x hx

theorem symmetric (w : Nat → ℝ) (x y : Nat) : charge w x y = charge w y x :=
  charge_symm w x y

theorem scale_invariant (w : Nat → ℝ) (c : ℝ) (hc : 0 < c) (x y : Nat) :
    charge (fun k => c * w k) x y = charge w x y := charge_scale w c hc x y

theorem request_charge (w : Nat → ℝ) (x y : Nat)
    (hw : ∀ k ∈ Finset.Icc (min x y) (max x y), 0 < w k) :
    1 ≤ charge w x y := charge_ge_one w x y hw

/-- The optimized weighted benchmark still pays for every request. -/
theorem optimal_request_charge (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (xs.length : ℝ) ≤ optimalCostFrom n p xs := length_le_optimalCostFrom n p xs hp valid

/-- Every positive weighting is an upper bound on the weight infimum. -/
theorem optimal_le (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (hw : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    optimalCostFrom n p xs ≤ costFrom w p xs := optimalCostFrom_le w n p xs hw hp valid

end RotationBST.WeightedFinger.Results

/-- info: abstract audit passed for `RotationBST.WeightedFinger.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.WeightedFinger.Results allowing [
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract]
