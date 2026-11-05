module

public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace RotationBST.LazyFinger

/-- Edge distance between ranks in a fixed BST: descend together until the
lowest common ancestor, then add the two remaining depths. Invalid ranks only
have totalized values; applications use ranks less than `t.size`. -/
def distance : Tree → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .node l r, x, y =>
    if x < l.size ∧ y < l.size then distance l x y
    else if l.size < x ∧ l.size < y then
      distance r (x - l.size - 1) (y - l.size - 1)
    else Tree.depth (.node l r) x + Tree.depth (.node l r) y

/-- Depth of the lowest common ancestor of two valid ranks. -/
def lcaDepth : Tree → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .node l r, x, y =>
    if x < l.size ∧ y < l.size then lcaDepth l x y + 1
    else if l.size < x ∧ l.size < y then
      lcaDepth r (x - l.size - 1) (y - l.size - 1) + 1
    else 0

/-- Lazy-finger cost from a specified initial key, including one per request. -/
def costFrom (t : Tree) : Nat → List Nat → Nat
  | _, [] => 0
  | p, x :: xs => 1 + distance t p x + costFrom t x xs

/-- The first search starts at the root. Request charges ensure repeated keys
still cost one, consistently with the rest of the library. -/
def cost : Tree → List Nat → Nat
  | .nil, xs => xs.length
  | .node l r, xs => costFrom (.node l r) l.size xs

/-- Best normalized lazy-finger cost among all shapes on `n` ordered keys.
The attainment theorem supplies a minimizing shape; this definition alone is
not an executable dynamic-programming algorithm. -/
noncomputable def optimalCost (n : Nat) (xs : List Nat) : Nat :=
  sInf {k | ∃ t : Tree, t.size = n ∧ cost t xs = k}

/-- Optimal fixed-tree cost with a specified initial finger. -/
noncomputable def optimalCostFrom (n p : Nat) (xs : List Nat) : Nat :=
  sInf {k | ∃ t : Tree, t.size = n ∧ costFrom t p xs = k}

end RotationBST.LazyFinger
