module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

namespace RotationBST.StaticTree

/-- Number of edges on an ordinary rank-search path. The empty case only makes
the function total; performance statements require existing keys. -/
def depth : Tree → Nat → Nat
  | .nil, _ => 0
  | .node l r, x =>
      if x < l.size then depth l x + 1
      else if x = l.size then 0
      else depth r (x - l.size - 1) + 1

/-- Search a fixed tree from its root each time, charging one per request and
one per downward pointer move. No rotations or return-to-root moves occur. -/
def cost (t : Tree) (xs : List Nat) : Nat :=
  (xs.map fun x => depth t x + 1).sum

end RotationBST.StaticTree
