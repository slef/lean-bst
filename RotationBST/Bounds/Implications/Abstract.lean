module

import RotationBST.Audit.Check
public import RotationBST.Bounds.Implications.AbstractBridge

@[expose] public section

/-! Algorithm-independent implications. The properties and costs appear in
`Bounds/WorkingSet/Abstract`, `Bounds/Abstract`,
`Bounds/DynamicFinger/Definitions/Abstract` and `Bounds/Logarithmic/Abstract`;
no splay hypothesis is used. -/
namespace RotationBST.Bounds

theorem workingSet_implies_staticOptimality (a : Algorithm) (h : HasWorkingSetBound a) :
    HasStaticOptimalityBound a :=
  h.staticOptimality a

theorem staticOptimality_implies_staticFinger (a : Algorithm) (h : HasStaticOptimalityBound a) :
    HasStaticFingerBound a :=
  h.staticFinger a

theorem workingSet_implies_staticFinger (a : Algorithm) (h : HasWorkingSetBound a) :
    HasStaticFingerBound a :=
  h.staticFinger a

theorem dynamicFinger_implies_staticFinger (a : Algorithm) (h : HasDynamicFingerBound a) :
    HasStaticFingerBound a :=
  h.staticFinger a

/-- Every distance between two of `n` keys is less than `n`, so the
static-finger sum is at most the logarithmic baseline. -/
theorem fingerCost_le_log (n f : Nat) (xs : List Nat) (hf : f < n) (valid : ∀ x ∈ xs, x < n) :
    fingerCost f xs ≤ logCost n xs :=
  fingerCost_le_logCost n f xs hf valid

theorem staticFinger_implies_logarithmic (a : Algorithm) (h : HasStaticFingerBound a) :
    HasLogarithmicBound a :=
  h.logarithmic a

end RotationBST.Bounds

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Bounds`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Bounds allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.DynamicFinger.Definitions.Abstract,
  RotationBST.Bounds.Logarithmic.Abstract]
