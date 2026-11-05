module

import RotationBST.Audit.Check
public import RotationBST.Structures.Treap.Order.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.TreapOrder.Results

/-- Every finite inorder interval has a treap for priorities in any linear
order. In particular priorities need not be next-touch times. -/
theorem exists_tree {α : Type} [LinearOrder α] (priority : Nat → α) (n lo : Nat) :
    ∃ t : Tree, t.size = n ∧ Heap priority t lo := heap_exists priority n lo

/-- Distinct priorities make that treap unique. -/
theorem unique_shape {α : Type} [LinearOrder α] (priority : Nat → α)
    (t u : Tree) (lo : Nat) (size : t.size = u.size)
    (ht : Heap priority t lo) (hu : Heap priority u lo)
    (unique : Set.InjOn priority (Set.Ico lo (lo + t.size))) : t = u :=
  heap_unique priority t u lo size ht hu unique

/-- The ancestor event is exactly an interval-minimum event. This deterministic
identity does not assume or assert a distribution on priorities. -/
theorem ancestor_minimum {α : Type} [LinearOrder α] (priority : Nat → α)
    (t : Tree) (lo a x : Nat) (heap : Heap priority t lo)
    (unique : Set.InjOn priority (Set.Ico lo (lo + t.size)))
    (ha : lo ≤ a ∧ a < lo + t.size) (hx : lo ≤ x ∧ x < lo + t.size) :
    a ∈ t.searchPath lo x ↔
      ∀ b, min a x ≤ b → b ≤ max a x → priority a ≤ priority b :=
  heap_ancestor_iff priority t lo a x heap unique ha hx

end RotationBST.Geometric.TreapOrder.Results

/-- info: abstract audit passed for `RotationBST.Geometric.TreapOrder.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.TreapOrder.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Rotation.Search.Abstract,
  RotationBST.Structures.Treap.Abstract]
