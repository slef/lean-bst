module

import RotationBST.Audit.Check
public import RotationBST.Bounds.Implications.AbstractBridge

@[expose] public section

/-! Algorithm-independent implications. The properties and costs appear in
`Bounds/WorkingSet/Abstract` and `Bounds/Abstract`; no splay hypothesis is used. -/
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

end RotationBST.Bounds

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Bounds`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Bounds allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract]
