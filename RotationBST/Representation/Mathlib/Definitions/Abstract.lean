module

public import RotationBST.Model.Abstract
public import Mathlib.Data.Tree.Basic

@[expose] public section

namespace RotationBST.Representation

/-- The elementary shape as Mathlib's standard binary tree with unit labels. -/
def toBinaryTree : Tree → BinaryTree Unit
  | .nil => .nil
  | .node l r => .node () (toBinaryTree l) (toBinaryTree r)

def fromBinaryTree : BinaryTree Unit → Tree
  | .nil => .nil
  | .node _ l r => .node (fromBinaryTree l) (fromBinaryTree r)

end RotationBST.Representation
