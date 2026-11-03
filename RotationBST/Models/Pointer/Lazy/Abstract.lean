module

import RotationBST.Audit.Check
public import RotationBST.Models.Pointer.Lazy.AbstractBridge

@[expose] public section

/-! Exchange rules and connected-region normalization for lazy simulation. The elementary endpoint-labelled
rotation programs are in `Lazy/Rotations/Abstract`. These results rearrange
rotations without adding any. The complete pointer-cost simulation is exposed in
`Models/Pointer/Abstract`. -/
namespace RotationBST.Pointer.Lazy.Results

variable {α : Type} {x y u v : α} {s t z : LabelledTree α}

theorem commute (first : RotateAt x y s t) (second : RotateAt u v t z)
    (disjoint : DisjointPairs x y u v) :
    ∃ q, RotateAt u v s q ∧ RotateAt x y q z :=
  Lazy.commute first second disjoint

/-- Independent rotations outside the requested key's color can be postponed.
The prefix still serves the request; the suffix restores the exact final tree. -/
theorem postpone_access (color : α → Bool) (ops : List (α × α)) (program : Trace s ops t)
    (uniform : ∀ e ∈ ops, color e.1 = color e.2)
    (root : rootKey? t = some x) (selected : color x = true) :
    ∃ q, LabelledTree.Access s q x (ops.filter fun e => color e.1).length ∧
      Trace q (ops.filter fun e => !(color e.1)) t ∧
      (ops.filter fun e => color e.1).length +
        (ops.filter fun e => !(color e.1)).length = ops.length :=
  Lazy.postpone_access color program uniform root selected

/-- Reshape a connected active region without entering its fringe subtrees. -/
theorem reshape (s t : Skeleton) (same : s.fringe = t.fringe) :
    ∃ k, k ≤ 16 * s.size ∧ Pointer.Trace ⟨s.tree, []⟩ ⟨t.tree, []⟩ k :=
  Skeleton.reshape s t same

end RotationBST.Pointer.Lazy.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Pointer.Lazy.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Lazy.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Rotations.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract]
