module

public import RotationBST.Algorithms.Tango.State.Defs

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- The reference tree with exactly the preferred edges left unmarked. This
specifies the component nesting independently of auxiliary-tree rotations. -/
def canonical : Tree → Nat → List Nat → MarkedTree
  | .nil, _, _ => .nil
  | .node l r, lo, past =>
      let left := canonical l lo past
      let right := canonical r (lo + l.size + 1) past
      match (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast? with
      | none => .node left right true true
      | some true => .node left right false true
      | some false => .node left right true false

end RotationBST.Tango.MarkedTree
