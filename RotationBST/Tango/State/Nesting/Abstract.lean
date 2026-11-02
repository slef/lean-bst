module

public import RotationBST.Tango.State.Canonical.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- Ordered nesting of auxiliary components. A branch's children are its fringe
components, in key order; auxiliary BST shape is deliberately absent. -/
inductive ComponentNesting where
  | empty
  | branch (children : List ComponentNesting)
  deriving Repr

/-- An empty BST is one empty fringe slot. -/
def ComponentNesting.fringe : ComponentNesting → List ComponentNesting
  | .empty => [.empty]
  | .branch children => children

/-- Number of inorder gaps in the represented BST, one more than its key count. -/
def ComponentNesting.span : ComponentNesting → Nat
  | .empty => 1
  | .branch children => (children.map ComponentNesting.span).sum

namespace MarkedTree

def nesting : MarkedTree → ComponentNesting
  | .nil => .empty
  | .node l r cl cr => .branch
      ((if cl then [nesting l] else (nesting l).fringe) ++
       (if cr then [nesting r] else (nesting r).fringe))

/-- Full maintenance invariant: the preferred-path partition, its root path,
and the ordered nesting prescribed by the reference tree. -/
def Maintains (s : MarkedTree) (reference : Tree) (past : List Nat) : Prop :=
  Represents s reference past ∧ s.nesting = (canonical reference 0 past).nesting

end MarkedTree
end RotationBST.Tango
