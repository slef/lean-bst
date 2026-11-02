module

public import RotationBST.Model.Abstract

@[expose] public section

namespace RotationBST.LabelledTree

/-- The usual local BST invariant: both children are BSTs, every key on the
left is smaller than the root, and every key on the right is larger. -/
def Ordered {α : Type} [LT α] : LabelledTree α → Prop
  | .nil => True
  | .node l x r => l.Ordered ∧ r.Ordered ∧
      (∀ y ∈ l.inorder, y < x) ∧ (∀ y ∈ r.inorder, x < y)

end RotationBST.LabelledTree
