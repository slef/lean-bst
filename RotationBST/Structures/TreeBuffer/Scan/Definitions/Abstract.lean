module

public import RotationBST.Models.Pointer.Walk.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Scan

/-- A buffer finger and a scan boundary. For forward scans, `next` is the first
unvisited cell; for reverse scans, it is one past the first unvisited cell.
Only a key, boundary counter, and direction bit are part of the scan state. -/
structure State where
  tree : Tree
  position : Nat
  next : Nat
  descending : Bool
  deriving DecidableEq

def State.Valid (s : State) : Prop := s.position < s.tree.size ∧ s.next ≤ s.tree.size

/-- The remaining list is a specification quantity, not additional scan storage. -/
def State.requests (s : State) : List Nat :=
  if s.descending then (List.range s.next).reverse else List.range' s.next (s.tree.size - s.next)

def State.target (s : State) : Nat := if s.descending then s.next - 1 else s.next

def State.afterVisit (s : State) : State :=
  { s with next := if s.descending then s.next - 1 else s.next + 1 }

/-- Remaining navigation and cell-visit work without further rotations. -/
def potential (s : State) : Nat := LazyFinger.costFrom s.tree s.position s.requests

/-- Other fingers may rotate after every primitive move. Cell visits cost one;
the two counters separate the scan's work from externally performed rotations. -/
inductive Step : State → State → Nat → Nat → Prop where
  | move {s : State} {a b : Pointer.Config} {y : Nat} :
      a.tree = s.tree → Pointer.Move a b → a.key? = some s.position → b.key? = some y →
      s.requests ≠ [] →
      LazyFinger.distance b.tree y s.target + 1 = LazyFinger.distance s.tree s.position s.target →
      Step s { s with tree := b.tree, position := y } 1 0
  | visit {s : State} : s.requests ≠ [] → s.position = s.target → Step s s.afterVisit 1 0
  | rotate {s : State} {t : Tree} : Rotate s.tree t → Step s { s with tree := t } 0 1

inductive Trace : State → State → Nat → Nat → Prop where
  | refl {s : State} : Trace s s 0 0
  | step {s t u : State} {k r h q : Nat} :
      Step s t k r → Trace t u h q → Trace s u (k + h) (r + q)

end RotationBST.TreeBuffer.Scan
