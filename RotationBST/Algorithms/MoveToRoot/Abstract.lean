module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.MoveToRoot.AbstractBridge

@[expose] public section

/-! The executable definition is in `Algorithm/Abstract`. Move-to-root serves
every existing rank with fewer rotations than there are nodes; it is the
constructive witness behind the existence results of the rotation model. -/
namespace RotationBST

namespace MoveToRoot.Results

/-- Move-to-root exposes the requested rank with a legal rotation trace, using
fewer than `size` rotations. -/
theorem correct (t : Tree) (x : Nat) (valid : x < t.size) :
    Access t (moveToRoot t x).1 x (moveToRoot t x).2 ∧ (moveToRoot t x).2 < t.size :=
  moveToRoot_correct t x valid

end MoveToRoot.Results

/-- A baseline algorithm, not splaying: single rotations move the request upward. -/
def moveToRootAlgorithm : Algorithm where
  step _ t x := moveToRoot t x
  correct _ t x hx := (moveToRoot_correct t x hx).1

end RotationBST

/-- info: abstract audit passed for `RotationBST.MoveToRoot.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.MoveToRoot.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.MoveToRoot.Algorithm.Abstract]
