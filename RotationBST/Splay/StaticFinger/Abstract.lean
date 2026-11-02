module

import RotationBST.AbstractAudit.Check
public import RotationBST.Splay.StaticFinger.AbstractBridge

@[expose] public section

/-! Fixed-finger distance is the absolute difference of implicit inorder ranks;
its cost and uniform constants are spelled out in `Bounds/Abstract`. -/
namespace RotationBST.Splay.Results

theorem staticFinger : HasStaticFingerBound algorithm :=
  Splay.hasWorkingSetBound.staticFinger algorithm

/-- When every key occurs, the startup allowance can be omitted. -/
theorem staticFinger_all_accessed (t : Tree) (xs : List Nat) (f : Nat)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 12 * Bounds.fingerCost f xs :=
  Bridge.staticFinger_all_accessed t xs f valid covers

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Online.Abstract,
  RotationBST.Bounds.Abstract]
