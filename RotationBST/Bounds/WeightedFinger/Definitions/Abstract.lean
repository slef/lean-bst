module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace RotationBST.WeightedFinger

/-- Inclusive interval mass; both endpoints contribute. -/
noncomputable def mass (w : Nat → ℝ) (x y : Nat) : ℝ :=
  ∑ k ∈ Finset.Icc (min x y) (max x y), w k

/-- The weighted dynamic-finger charge of Iacono and Langerman,
arXiv:1810.01785. Bound statements require positive weights. -/
noncomputable def charge (w : Nat → ℝ) (x y : Nat) : ℝ :=
  1 + Real.logb 2 (mass w x y / min (w x) (w y))

/-- Charges for consecutive requests, with the preceding request explicit. -/
noncomputable def costFrom (w : Nat → ℝ) : Nat → List Nat → ℝ
  | _, [] => 0
  | p, x :: xs => charge w p x + costFrom w x xs

/-- Infimum over positive weights on the key universe. No attainment of this
real-valued infimum is assumed. The comparison theorems require valid requests
and a valid initial finger in this universe. -/
noncomputable def optimalCostFrom (n p : Nat) (xs : List Nat) : ℝ :=
  sInf {c | ∃ w : Nat → ℝ, (∀ k < n, 0 < w k) ∧ costFrom w p xs = c}

end RotationBST.WeightedFinger
