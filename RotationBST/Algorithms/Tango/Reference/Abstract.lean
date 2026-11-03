module

public import RotationBST.Bounds.Interleave.Definitions.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- A balanced reference BST on exactly `n` implicit inorder keys. Its two
subtrees differ in size by at most one. -/
def balanced : Nat → Tree
  | 0 => .nil
  | n + 1 => .node (balanced ((n + 1) / 2)) (balanced (n / 2))
termination_by n => n

end RotationBST.Tango
