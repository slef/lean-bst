module

public import RotationBST.Algorithms.Tango.State.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- Number of inorder gaps in the represented BST, one more than its key count. -/
def ComponentNesting.span : ComponentNesting → Nat
  | .empty => 1
  | .branch children => (children.map ComponentNesting.span).sum

end RotationBST.Tango
