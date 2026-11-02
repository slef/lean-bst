module

import RotationBST.AbstractAudit.Check
public import RotationBST.Bounds.Implications.AbstractBridge

@[expose] public section

/-! Algorithm-independent implications. The properties and costs appear in
`WorkingSet/Abstract` and `Bounds/Abstract`; no splay hypothesis is used. -/
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
#check_bst_abstract RotationBST.Bounds allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract]
