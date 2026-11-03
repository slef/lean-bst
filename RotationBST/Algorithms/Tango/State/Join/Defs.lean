module

public import RotationBST.Algorithms.Tango.State.Splay.Defs

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Merge the last attached component after a maximum splay. -/
def joinBack (s : MarkedTree) : MarkedTree × Nat :=
  let result := s.splayRoot (s.region.size - 1)
  match result.1 with
  | .nil => result
  | .node l r cl _ => (.node l r cl false, result.2)

/-- Merge the first attached component after a minimum splay. -/
def joinFront (s : MarkedTree) : MarkedTree × Nat :=
  let result := s.splayRoot 0
  match result.1 with
  | .nil => result
  | .node l r _ cr => (.node l r false cr, result.2)

/-- Merge an interior fringe component by exposing its predecessor, then
joining the first component attached to the remaining right subtree. -/
def joinInterior (s : MarkedTree) (index : Nat) : MarkedTree × Nat :=
  let result := s.splayRoot (index - 1)
  match result.1 with
  | .nil => result
  | .node l r cl cr =>
      let right := r.joinFront
      (.node l right.1 cl cr, result.2 + right.2)

end RotationBST.Tango.MarkedTree
