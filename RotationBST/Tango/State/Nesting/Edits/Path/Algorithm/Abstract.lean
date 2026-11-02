module

public import RotationBST.Tango.State.Context.Fringe.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Compile a reference-edge cut inside an unmarked path to active-rank
boundaries in the actual auxiliary tree. Empty children need no edit. -/
def markInPath (s : MarkedTree) (fs : List Context.Frame) (f : Context.Frame) (child : MarkedTree) :
    MarkedTree × Nat :=
  if child = .nil then (s, 0)
  else
    let first := (Context.before (f :: fs)).length
    s.cutInterval first (first + child.region.size)

/-- Compile the inverse reference-edge change to the corresponding fringe slot. -/
def unmarkInPath (s : MarkedTree) (fs : List Context.Frame) (f : Context.Frame) : MarkedTree × Nat :=
  s.mergeAt (Context.before (f :: fs)).length

/-- Switch a reference preference within one component: cut the old preferred
child, then merge the new one. `left` names the old preference. -/
def switchInPath (s : MarkedTree) (fs : List Context.Frame) (l r : MarkedTree) (left : Bool) :
    MarkedTree × Nat :=
  if left then
    let cut := s.markInPath fs (.left r false true) l
    let joined := cut.1.unmarkInPath fs (.right l false true)
    (joined.1, cut.2 + joined.2)
  else
    let cut := s.markInPath fs (.right l false true) r
    let joined := cut.1.unmarkInPath fs (.left r false true)
    (joined.1, cut.2 + joined.2)

end RotationBST.Tango.MarkedTree
