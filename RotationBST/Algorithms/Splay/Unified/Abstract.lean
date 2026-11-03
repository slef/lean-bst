module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Unified.AbstractBridge

@[expose] public section

/-! The 1985 fixed-finger unified theorem. `Bounds/Unified/Abstract` spells out
its per-access minimum of frequency, finger, and working-set logarithms.
This is distinct from the later dynamic unified-bound conjecture. -/
namespace RotationBST.Splay.Results
open Bounds

theorem unified (t : Tree) (xs : List Nat) (f : Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.totalCost t xs : ℝ) ≤ 11 * unifiedSum t.size f xs [] xs +
      8 * (t.size : ℝ) * (1 + (t.size.log2 : ℝ)) :=
  Splay.unified_bound t xs f valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Splay.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract,
  RotationBST.Bounds.Unified.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract]
