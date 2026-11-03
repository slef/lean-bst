module

public import RotationBST.Algorithms.Tango.State.Defs

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Fill the inorder gaps of an auxiliary shape with whole marked subtrees.
The unused suffix is returned, so reconstruction is executable by one traversal.
A missing fringe entry is treated as an empty subtree. -/
def fill : Tree → List MarkedTree → MarkedTree × List MarkedTree
  | .nil, [] => (.nil, [])
  | .nil, t :: rest => (t, rest)
  | .node a b, fringe =>
      let (l, rest) := fill a fringe
      let (r, unused) := fill b rest
      (.node l r (decide (a = .nil)) (decide (b = .nil)), unused)

/-- Reassemble a whole marked BST from an auxiliary shape and ordered fringe. -/
def rebuild (shape : Tree) (fringe : List MarkedTree) : MarkedTree := (fill shape fringe).1

end RotationBST.Tango.MarkedTree
