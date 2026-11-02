module

public import RotationBST.Tango.Definitions.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- First setting plus subsequent changes of an observed region label. -/
def runs (trace : List Bool) : Nat :=
  match trace with
  | [] => 0
  | _ :: _ => 1 + alternations trace

/-- Number of reference nodes whose regions have been observed at least once.
Counting leaf labels is harmless and gives an upper bound for child settings. -/
def initializations : Tree → List Nat → Nat
  | .nil, _ => 0
  | .node l r, xs =>
      (if regions l.size (l.size + 1 + r.size) xs = [] then 0 else 1) +
      initializations l (leftRequests l.size xs) + initializations r (rightRequests l.size xs)

/-- All preferred-region settings, including the first setting of each node. -/
def preferenceChanges : Tree → List Nat → Nat
  | .nil, _ => 0
  | .node l r, xs => runs (regions l.size (l.size + 1 + r.size) xs) +
      preferenceChanges l (leftRequests l.size xs) + preferenceChanges r (rightRequests l.size xs)

end RotationBST.Tango
