module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Balance.AbstractBridge

@[expose] public section

namespace RotationBST.Splay.Results

/-- Balance theorem, including requests and the arbitrary initial shape. -/
theorem balance (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.totalCost t xs : ℝ) ≤
      (xs.length : ℝ) * (2 + 3 * Real.logb 2 t.size) +
      (t.size : ℝ) * Real.logb 2 t.size :=
  Splay.balance t xs valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract]
