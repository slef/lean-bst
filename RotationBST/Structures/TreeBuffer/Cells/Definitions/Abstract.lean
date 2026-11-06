module

public import RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract
public import RotationBST.Models.Labelled.Metadata.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

/-- One payload per existing node, rendered by `Metadata.label`. Values outside
the current finite key universe are unobservable through the cell operations. -/
structure State (α : Type) where
  scan : Scan.State
  data : Nat → α

/-- An observable cell access. Events form a specification trace, not additional
runtime storage; reads return a value and writes receive a value from their caller. -/
inductive Event (α : Type) where
  | read (key : Nat) (value : α)
  | write (key : Nat) (value : α)
  deriving DecidableEq

def Event.key {α : Type} : Event α → Nat
  | .read key _ => key
  | .write key _ => key

def Event.value {α : Type} : Event α → α
  | .read _ value => value
  | .write _ value => value

/-- Payload I/O is permitted only at the finger's existing node. Navigation is
charged per primitive and follows the scan rule; rotations by other fingers
preserve every payload. Each cell read or write costs one visit unit. -/
inductive Step {α : Type} : State α → State α → Option (Event α) → Nat → Nat → Prop where
  | navigate {s : State α} {a b : Pointer.Config} {y : Nat} :
      a.tree = s.scan.tree → Pointer.Move a b → a.key? = some s.scan.position → b.key? = some y →
      s.scan.requests ≠ [] →
      LazyFinger.distance b.tree y s.scan.target + 1 = LazyFinger.distance s.scan.tree s.scan.position s.scan.target →
      Step s ⟨{ s.scan with tree := b.tree, position := y }, s.data⟩ none 1 0
  | read {s : State α} : s.scan.position < s.scan.tree.size → s.scan.requests ≠ [] →
      s.scan.position = s.scan.target →
      Step s ⟨s.scan.afterVisit, s.data⟩ (some (.read s.scan.position (s.data s.scan.position))) 1 0
  | write {s : State α} (value : α) : s.scan.position < s.scan.tree.size → s.scan.requests ≠ [] →
      s.scan.position = s.scan.target →
      Step s ⟨s.scan.afterVisit, Function.update s.data s.scan.position value⟩
        (some (.write s.scan.position value)) 1 0
  | rotate {s : State α} {t : Tree} : Rotate s.scan.tree t →
      Step s ⟨{ s.scan with tree := t }, s.data⟩ none 0 1

inductive Trace {α : Type} : State α → State α → List (Event α) → Nat → Nat → Prop where
  | refl {s : State α} : Trace s s [] 0 0
  | step {s t u : State α} {event : Option (Event α)} {events : List (Event α)} {k r h q : Nat} :
      Step s t event k r → Trace t u events h q → Trace s u (event.toList ++ events) (k + h) (r + q)

/-- The mathematical effect of a stream of writes supplied in key order. The
actual machine writes only at its cursor; it does not evaluate this recursion
as a sequence of free random-access memory operations. -/
def writeMany {α : Type} (target : Nat → α) : List Nat → (Nat → α) → (Nat → α)
  | [], data => data
  | x :: xs, data => writeMany target xs (Function.update data x (target x))

/-- Specification of the data effect of an observable I/O stream. -/
def effect {α : Type} (data : Nat → α) : List (Event α) → (Nat → α)
  | [] => data
  | .read _ _ :: events => effect data events
  | .write key value :: events => effect (Function.update data key value) events

end RotationBST.TreeBuffer.Cells
