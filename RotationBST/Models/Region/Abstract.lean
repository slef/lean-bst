module

public import RotationBST.Structures.Treap.Abstract
public import RotationBST.Models.Pointer.Lazy.Skeleton.Abstract

@[expose] public section
namespace RotationBST.Arboral

abbrev Region := Pointer.Lazy.Skeleton

namespace Region

/-- Absolute inorder ranks of the nodes which may be rearranged. -/
def keys : Region → Nat → Finset Nat
  | .hole _, _ => ∅
  | .node l r, lo => insert (lo + l.tree.size)
      (keys l lo ∪ keys r (lo + l.tree.size + 1))

/-- Untouched fringe subtrees, with their absolute inorder offsets. -/
def holes : Region → Nat → List (Nat × Tree)
  | .hole t, lo => [(lo, t)]
  | .node l r, lo => holes l lo ++ holes r (lo + l.tree.size + 1)

/-- Reordering preserves all active keys and the exact untouched fringe. -/
def Same (s t : Region) (lo : Nat) : Prop :=
  s.tree.size = t.tree.size ∧ keys s lo = keys t lo ∧ holes s lo = holes t lo

/-- Stop at untouched roots; on a next-touch treap this selects the whole row. -/
def project (P : Finset Point) (time : Nat) : Tree → Nat → Region
  | .nil, _ => .hole .nil
  | .node l r, lo =>
      if (lo + l.size, time) ∈ P then
        .node (project P time l lo) (project P time r (lo + l.size + 1))
      else .hole (.node l r)

/-- Heap order on the active nodes, ignoring the roots of fringe subtrees. -/
def ActiveHeap (priority : Nat → WithTop Nat) : Region → Nat → Prop
  | .hole _, _ => True
  | .node l r, lo =>
      (∀ x ∈ keys (.node l r) lo, priority (lo + l.tree.size) ≤ priority x) ∧
      ActiveHeap priority l lo ∧ ActiveHeap priority r (lo + l.tree.size + 1)

end Region
end RotationBST.Arboral
