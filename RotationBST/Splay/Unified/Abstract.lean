module

import RotationBST.AbstractAudit.Check
public import RotationBST.Splay.Unified.AbstractBridge

@[expose] public section

/-! The 1985 fixed-finger unified theorem. `Bounds/Unified/Abstract` spells out
its per-access minimum of frequency, finger, and working-set logarithms.
This is distinct from the later dynamic unified-bound conjecture. -/
namespace RotationBST.Splay.Results

theorem unified (t : Tree) (xs : List Nat) (f : Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.totalCost t xs : ℝ) ≤ 11 * unifiedSum t.size f xs [] xs +
      8 * (t.size : ℝ) * (1 + (t.size.log2 : ℝ)) :=
  Splay.unified_bound t xs f valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Online.Abstract,
  RotationBST.Bounds.Unified.Abstract,
  RotationBST.WorkingSet.Abstract]
