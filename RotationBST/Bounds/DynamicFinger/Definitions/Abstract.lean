module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Dist
public import RotationBST.Models.Online.Abstract

@[expose] public section
namespace RotationBST.Bounds

/-- Dynamic-finger charges for consecutive requests, including a unit per
request. The predecessor of the first request is supplied explicitly. -/
noncomputable def dynamicFingerCostFrom : Nat → List Nat → ℝ
  | _, [] => 0
  | p, x :: xs => 1 + Real.logb 2 (Nat.dist p x + 1 : Nat) + dynamicFingerCostFrom x xs

end RotationBST.Bounds

namespace RotationBST

/-- The dynamic-finger property. The bound holds for every start key `p`; the
choice of `p` changes the sum by at most `1 + log₂ n`, which the startup term
absorbs, so fixing `p` instead would give an equivalent property. -/
def HasDynamicFingerBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs p, p < t.size → (∀ x ∈ xs, x < t.size) →
    (a.totalCost t xs : ℝ) ≤ (C : ℝ) * Bounds.dynamicFingerCostFrom p xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ))

end RotationBST
