module

import RotationBST.Audit.Check
public import RotationBST.Bounds.Interleave.AbstractBridge

@[expose] public section
namespace RotationBST.Wilber.Results

/-- Wilber's interleave quantity lower-bounds every ASS solution. The reference
tree is arbitrary; it need not be balanced. -/
theorem interleave_lower_bound {n : Nat} {xs : List Nat} (reference : Tree)
    (size : reference.size = n) (E : Arboral.Offline n xs) :
    interleave reference xs ≤ 2 * E.points.card := Wilber.interleave_le_ass reference size E

/-- Lower bound against every offline execution in the simplified BST model. -/
theorem rotation_lower_bound (reference : Tree) {s t : Tree} {xs : List Nat} {r : Nat}
    (size : reference.size = s.size) (execution : RotationBST.Execution s xs t r) :
    interleave reference xs ≤ 4 * r + 2 * xs.length :=
  Wilber.interleave_le_rotations reference size execution

/-- Lower bound against conventional pointer-and-rotation executions. -/
theorem pointer_lower_bound (reference : Tree) {s t : Tree} {xs : List Nat} {cost : Nat}
    (size : reference.size = s.size) (execution : Pointer.Execution s xs t cost) :
    interleave reference xs ≤ 12 * cost := Wilber.interleave_le_pointers reference size execution

end RotationBST.Wilber.Results

/-- info: abstract audit passed for `RotationBST.Wilber.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Wilber.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract, RotationBST.Models.Geometric.Offline.Abstract]
