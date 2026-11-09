module

public import RotationBST.Models.Online.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-! The logarithmic baseline `m(1 + log₂ n)`: what a balanced tree pays on
every sequence of `m` requests over `n` keys, and what every static tree pays
on some sequence. -/
namespace RotationBST

/-- One unit plus `log₂ n` per request. -/
noncomputable def Bounds.logCost (n : Nat) (xs : List Nat) : ℝ :=
  (xs.length : ℝ) * (1 + Real.logb 2 n)

/-- Logarithmic amortized cost per request, with the usual startup allowance. -/
def HasLogarithmicBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
    (a.totalCost t xs : ℝ) ≤ (C : ℝ) * Bounds.logCost t.size xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ))

end RotationBST
