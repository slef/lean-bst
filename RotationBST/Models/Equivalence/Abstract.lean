module

import RotationBST.Audit.Check
public import RotationBST.Models.Equivalence.AbstractBridge

@[expose] public section

/-! The geometric model is equivalent to the BST models. Offline, point
counts and BST costs agree up to the displayed constants; online, every
geometric algorithm has a causal BST counterpart (proved in
`Algorithms/Simulation`). Pointer-versus-rotation equivalence is in
`Models/Pointer/Abstract`; labels-versus-shapes in `Models/Labelled/Abstract`. -/
namespace RotationBST.Geometric.Equivalence.Results

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

/-- Online: every online geometric algorithm has one causal BST policy, valid
from all initial shapes, with constant rotation cost per added point and a
linear initialization allowance. The policy is fixed before the request sequence. -/
theorem online_bst (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6018 * n :=
  Online.Supernode.uniform_online_policy n A

end RotationBST.Geometric.Equivalence.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Equivalence.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Equivalence.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract, RotationBST.Models.Region.View.Abstract,
  RotationBST.Structures.Treap.Abstract, RotationBST.Models.Region.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Model]
