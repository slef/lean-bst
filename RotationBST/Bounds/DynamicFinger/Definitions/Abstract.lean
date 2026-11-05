module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Dist

@[expose] public section
namespace RotationBST.Bounds

/-- Dynamic-finger charges for consecutive requests, including a unit per
request. The predecessor of the first request is supplied explicitly. -/
noncomputable def dynamicFingerCostFrom : Nat → List Nat → ℝ
  | _, [] => 0
  | p, x :: xs => 1 + Real.logb 2 (Nat.dist p x + 1 : Nat) + dynamicFingerCostFrom x xs

end RotationBST.Bounds
