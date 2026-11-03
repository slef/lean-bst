module

public import RotationBST.Algorithms.Tango.State.Abstract

@[expose] public section
namespace RotationBST.Tango
namespace MarkedTree

/-- Entire marked subtrees attached to the root component, in inorder. -/
def fringe : MarkedTree → List MarkedTree
  | .nil => [.nil]
  | .node l r cl cr => (if cl then [l] else l.fringe) ++ (if cr then [r] else r.fringe)

/-- The same marked fringe with absolute inorder offsets. -/
def fringeAt : MarkedTree → Nat → List (Nat × MarkedTree)
  | .nil, lo => [(lo, .nil)]
  | .node l r cl cr, lo =>
      (if cl then [(lo, l)] else l.fringeAt lo) ++
      (if cr then [(lo + l.tree.size + 1, r)] else r.fringeAt (lo + l.tree.size + 1))

end MarkedTree
end RotationBST.Tango
