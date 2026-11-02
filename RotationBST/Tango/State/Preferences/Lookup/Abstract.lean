module

public import RotationBST.Tango.State.Context.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Locate a reference key by inorder rank, returning its node and the ancestor
context needed to change its preference. Invalid ranks return `none`. -/
def locateKey : MarkedTree → Nat → Option (MarkedTree × List Context.Frame)
  | .nil, _ => none
  | .node l r cl cr, key =>
      if key < l.tree.size then
        (locateKey l key).map fun p => (p.1, p.2 ++ [.left r cl cr])
      else if key = l.tree.size then some (.node l r cl cr, [])
      else (locateKey r (key - l.tree.size - 1)).map fun p => (p.1, p.2 ++ [.right l cr cl])

end RotationBST.Tango.MarkedTree
