module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Equivalence.Exact

@[expose] public section
namespace RotationBST.Arboral.Results

/-- Exact point-count equivalence with rooted-subtree BST executions.
The initial tree is free; the conversion is offline. -/
theorem ass_iff_region_execution (n : Nat) (xs : List Nat) (cost : Nat) :
    (∃ E : Offline n xs, E.points.card = cost) ↔
      ∃ s t, s.size = n ∧ RegionExecution s xs t cost := offline_iff_regions n xs cost

/-- A rotation execution has a geometric solution of comparable total cost. -/
theorem rotations_to_ass {s t : Tree} {xs : List Nat} {r : Nat}
    (execution : RotationBST.Execution s xs t r) :
    ∃ E : Offline s.size xs, E.points.card ≤ 2 * r + xs.length :=
  rotations_to_offline execution

/-- Every ASS solution gives a rotation algorithm from any prescribed initial
shape. The additive term pays for initialization; no final shape is prescribed. -/
theorem ass_to_rotations (s : Tree) (xs : List Nat) (E : Offline s.size xs) :
    ∃ t r, RotationBST.Execution s xs t r ∧
      xs.length + r ≤ 2 * s.size + 99 * E.points.card := offline_from_initial s xs E

/-- The conventional pointer model also maps to geometry at constant cost. -/
theorem pointers_to_ass {s t : Tree} {xs : List Nat} {cost : Nat}
    (execution : Pointer.Execution s xs t cost) :
    ∃ E : Offline s.size xs, E.points.card ≤ 6 * cost := pointer_to_offline execution

/-- Without fixing the initial tree, the geometric solution has a pointer
realization with no additive initialization term. This construction is offline. -/
theorem ass_to_pointers {n : Nat} {xs : List Nat} (E : Offline n xs) :
    ∃ s t cost, s.size = n ∧ Pointer.Execution s xs t cost ∧ cost ≤ 33 * E.points.card :=
  offline_to_pointer E

end RotationBST.Arboral.Results

#check_bst_abstract RotationBST.Arboral.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Pointer.Machine.Abstract,
  RotationBST.Arboral.Definitions.Abstract, RotationBST.Arboral.Online.Abstract,
  RotationBST.Arboral.Offline.Abstract, RotationBST.Arboral.View.Abstract,
  RotationBST.Arboral.Treap.Abstract, RotationBST.Arboral.Treap.Regions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces, RotationBST.Pointer.Model]
