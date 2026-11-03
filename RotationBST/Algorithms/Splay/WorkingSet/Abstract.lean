module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.WorkingSet.AbstractBridge

@[expose] public section

/-! Working-set numbers, first-use convention, and integer-log sum are defined
in `Bounds/WorkingSet/Abstract`. This bound counts rotations; normalization adds the
request count, already bounded by the working-set sum. -/
namespace RotationBST.Splay.Results

theorem workingSet (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    algorithm.cost t xs ≤ 10 * workingSetSum t.size [] xs +
      6 * t.size * (1 + t.size.log2) :=
  Splay.workingSet_bound t xs valid

theorem hasWorkingSetBound : HasWorkingSetBound algorithm :=
  Splay.hasWorkingSetBound

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract]
