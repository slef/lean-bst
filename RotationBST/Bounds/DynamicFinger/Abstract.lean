module

import RotationBST.Audit.Check
public import RotationBST.Bounds.DynamicFinger.AbstractBridge

@[expose] public section

/-! Dynamic finger against static finger, as an inequality between sequence
costs. `Definitions/Abstract` gives the dynamic-finger sum and property;
`Bounds/Abstract` gives the static-finger sum. -/
namespace RotationBST.Bounds

/-- For every finger `f`, start key `p` and sequence, the dynamic-finger sum is
at most twice the static-finger sum, plus the start key's own finger term. -/
theorem dynamicFinger_le_fingerCost (f p : Nat) (xs : List Nat) :
    dynamicFingerCostFrom p xs ≤
      2 * fingerCost f xs + Real.logb 2 (Nat.dist p f + 1 : Nat) :=
  dynamicFingerCostFrom_le_fingerCost f p xs

/-- Starting at the finger, the start term vanishes. -/
theorem dynamicFinger_le_fingerCost_self (f : Nat) (xs : List Nat) :
    dynamicFingerCostFrom f xs ≤ 2 * fingerCost f xs :=
  dynamicFingerCostFrom_finger_le f xs

end RotationBST.Bounds

/-- info: abstract audit passed for `RotationBST.Bounds`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Bounds allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.DynamicFinger.Definitions.Abstract]
