module

public import RotationBST.Tango.State.Context.Abstract

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- Locate an inorder fringe slot and its ancestor context. The index
identifies an occurrence, even when several attached subtrees are identical. -/
def locateIndex : MarkedTree → Nat → Option (MarkedTree × List Frame)
  | .nil, i => if i = 0 then some (.nil, []) else none
  | .node l r cl cr, i =>
      let leftCount := (if cl then [l] else l.fringe).length
      if i < leftCount then
        if cl then some (l, [.left r true cr])
        else (locateIndex l i).map fun p => (p.1, p.2 ++ [.left r false cr])
      else
        if cr then
          if i - leftCount = 0 then some (r, [.right l true cl]) else none
        else (locateIndex r (i - leftCount)).map fun p => (p.1, p.2 ++ [.right l false cl])

/-- Apply a concrete local update at a specified fringe occurrence. An absent
slot leaves the whole state unchanged and reports zero rotations. -/
def editFringe (s : MarkedTree) (i : Nat) (edit : MarkedTree → MarkedTree × Nat) : MarkedTree × Nat :=
  match locateIndex s i with
  | none => (s, 0)
  | some (child, fs) =>
      let result := edit child
      (plug fs result.1, result.2)

end RotationBST.Tango.Context
