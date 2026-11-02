module

import RotationBST.AbstractAudit.Check
public import RotationBST.Splay.Snapshot.AbstractBridge

@[expose] public section

/-! The snapshot theorem. `Snapshot/Definitions/Abstract` defines independent
requests and uniform stopping by finite sums. The resulting tree is then used
as a static BST. Zero-probability keys are allowed. -/
namespace RotationBST.Splay.Results

theorem snapshot (t : Tree) (p : Nat → ℝ) (nonnegative : ∀ i, 0 ≤ p i)
    (normalized : ∑ i ∈ Finset.range t.size, p i = 1) (m : Nat) (positive : 0 < m) :
    snapshotMean t.size p t m ≤ 5 + 3 * probabilityEntropy t.size p +
      (t.size : ℝ) * (1 + Real.logb 2 t.size) / m :=
  Splay.snapshot_bound t p nonnegative normalized m positive

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Model.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Snapshot.Definitions.Abstract]
