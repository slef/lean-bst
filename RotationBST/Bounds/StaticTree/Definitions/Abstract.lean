module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

namespace RotationBST.StaticTree

/-- Search a fixed tree from its root each time, charging one per request and
one per downward pointer move (the rank's `Tree.depth`). No rotations or
return-to-root moves occur. -/
def cost (t : Tree) (xs : List Nat) : Nat :=
  (xs.map fun x => t.depth x + 1).sum

end RotationBST.StaticTree
