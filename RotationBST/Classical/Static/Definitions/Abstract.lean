module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! The perfectly balanced search tree on `n` keys. It has the same recursion as
`Tango.balanced`, which `Classical` cannot import (it sits below
`Algorithms`); the two definitions are textually identical. -/
namespace RotationBST.Classical.Static

/-- The root takes the middle rank; the left subtree gets `⌈(n-1)/2⌉` keys and
the right subtree `⌊(n-1)/2⌋`, so the two sizes differ by at most one. -/
def balanced : Nat → Tree
  | 0 => .nil
  | n + 1 => .node (balanced ((n + 1) / 2)) (balanced (n / 2))
termination_by n => n

/-- The number of nodes on a longest root-to-leaf path (`0` for the empty tree). -/
def height : Tree → Nat
  | .nil => 0
  | .node l r => max (height l) (height r) + 1

end RotationBST.Classical.Static
