module

public import RotationBST.Tango.State.Cut.Abstract
public import RotationBST.Tango.State.Join.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Detach a proper nonempty active interval using the appropriate boundary cuts. -/
def cutInterval (s : MarkedTree) (first pastLast : Nat) : MarkedTree × Nat :=
  if first = 0 then s.cutPrefix pastLast
  else if pastLast = s.region.size then s.cutSuffix first
  else s.cutInterior first pastLast

/-- Merge the fringe component at an inorder gap, including either end gap. -/
def mergeAt (s : MarkedTree) (index : Nat) : MarkedTree × Nat :=
  if index = 0 then s.joinFront
  else if index = s.region.size then s.joinBack
  else s.joinInterior index

end RotationBST.Tango.MarkedTree
