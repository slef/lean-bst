module

public import RotationBST.Tango.State.Splay.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Detach the first `count` active keys: splay the following boundary key and
mark its left edge. The verified contract requires a nonempty proper prefix. -/
def cutPrefix (s : MarkedTree) (count : Nat) : MarkedTree × Nat :=
  let result := s.splayRoot count
  match result.1 with
  | .nil => result
  | .node l r _ cr => (.node l r true cr, result.2)

/-- Detach active ranks from `first` onward by exposing their predecessor and
marking its right edge. -/
def cutSuffix (s : MarkedTree) (first : Nat) : MarkedTree × Nat :=
  let result := s.splayRoot (first - 1)
  match result.1 with
  | .nil => result
  | .node l r cl _ => (.node l r cl true, result.2)

/-- Detach the interior active-rank interval `[first, pastLast)`: expose its
predecessor, then perform a prefix cut in the remaining right component. -/
def cutInterior (s : MarkedTree) (first pastLast : Nat) : MarkedTree × Nat :=
  let result := s.splayRoot (first - 1)
  match result.1 with
  | .nil => result
  | .node l r cl cr =>
      let right := r.cutPrefix (pastLast - first)
      (.node l right.1 cl cr, result.2 + right.2)

end RotationBST.Tango.MarkedTree
