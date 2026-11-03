module

public import RotationBST.Models.Region.Abstract

/-! Internal definitions used by the treap and region proofs. -/

@[expose] public section
namespace RotationBST.Geometric

namespace Region
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
end RotationBST.Geometric
