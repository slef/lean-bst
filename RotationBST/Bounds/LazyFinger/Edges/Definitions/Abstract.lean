module

public import RotationBST.Bounds.LazyFinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.LazyFinger

/-- Whether a transition crosses the boundary of the half-open rank interval.
This is exactly the use of the edge connecting that subtree to its parent. -/
def cut (lo hi x y : Nat) : Nat :=
  if (lo ≤ x ∧ x < hi) ↔ (lo ≤ y ∧ y < hi) then 0 else 1

/-- Sum a boundary toll over the intervals of all nonempty subtrees, including
this tree itself. Its incoming edge is included; set the full-universe toll to
zero when both endpoints are inside the tree. -/
def intervalCost (w : Nat → Nat → Nat) : Tree → Nat → Nat
  | .nil, _ => 0
  | .node l r, lo =>
      w lo (lo + (.node l r : Tree).size) +
        intervalCost w l lo + intervalCost w r (lo + l.size + 1)

/-- Movement within a subtree, including its incoming edge. Endpoints may lie
outside the subtree, which is essential for decomposing a global sequence. -/
def edgeMovement (t : Tree) (lo x y : Nat) : Nat :=
  intervalCost (fun a b => cut a b x y) t lo

/-- Boundary crossings of a sequence with an explicit initial key. -/
def crossings (lo hi : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | p, x :: xs => cut lo hi p x + crossings lo hi x xs

end RotationBST.LazyFinger
