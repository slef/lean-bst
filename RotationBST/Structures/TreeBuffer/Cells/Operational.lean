module

public import RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Scan.Progress
public import RotationBST.Models.Labelled.Metadata.Representation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

/-- Invert a navigation event without fixing the dependent output data map. -/
theorem navigate_inv {α : Type} {s t : State α} (step : Step s t none 1 0) :
    ∃ a b y, a.tree = s.scan.tree ∧ Pointer.Move a b ∧ a.key? = some s.scan.position ∧ b.key? = some y ∧
      s.scan.requests ≠ [] ∧
      LazyFinger.distance b.tree y s.scan.target + 1 = LazyFinger.distance s.scan.tree s.scan.position s.scan.target ∧
      t.scan = { s.scan with tree := b.tree, position := y } := by
  cases step with
  | navigate tree move key next pending closer => exact ⟨_, _, _, tree, move, key, next, pending, closer, rfl⟩

theorem read_scan {α : Type} {s t : State α} {x : Nat} {value : α} {w r : Nat}
    (step : Step s t (some (.read x value)) w r) : t.scan = s.scan.afterVisit := by
  cases step
  rfl

theorem Step.scan {α : Type} {s t : State α} {event : Option (Event α)} {k r : Nat}
    (step : Step s t event k r) : Scan.Step s.scan t.scan k r := by
  cases step with
  | navigate tree move key next pending closer => exact .move tree move key next pending closer
  | read _ pending arrived => exact .visit pending arrived
  | write _ _ pending arrived => exact .visit pending arrived
  | rotate rotation => exact .rotate rotation

theorem Trace.scan {α : Type} {s t : State α} {events : List (Event α)} {k r : Nat}
    (trace : Trace s t events k r) : Scan.Trace s.scan t.scan k r := by
  induction trace with
  | refl => exact .refl
  | step first _ ih => exact .step first.scan ih

/-- Every read returns the actual payload at the currently touched labelled node. -/
theorem read_at {α : Type} {s t : State α} {x : Nat} {value : α} {k r : Nat}
    (step : Step s t (some (.read x value)) k r) :
    x = s.scan.position ∧ value = s.data x ∧ Metadata.At (Metadata.label s.data s.scan.tree 0) x value := by
  cases step with
  | read present _ _ => exact ⟨rfl, rfl, Metadata.label_at _ _ _ _ (Nat.zero_le _) (by simpa using present)⟩

/-- A write changes only the payload of the currently touched node. -/
theorem write_at {α : Type} {s t : State α} {x : Nat} {value : α} {k r : Nat}
    (step : Step s t (some (.write x value)) k r) :
    x = s.scan.position ∧
      Metadata.Write (Metadata.label s.data s.scan.tree 0) x value (Metadata.label t.data t.scan.tree 0) ∧
      (∀ y, y ≠ x → t.data y = s.data y) := by
  cases step with
  | write value present _ _ =>
    exact ⟨rfl, Metadata.label_write _ value _ _ _ (Nat.zero_le _) (by simpa using present),
      fun y different => Function.update_of_ne different _ _⟩

/-- The cell-access keys form exactly a prefix of the pending scan. -/
theorem Step.requests {α : Type} {s t : State α} {event : Option (Event α)} {k r : Nat}
    (step : Step s t event k r) : s.scan.requests = (event.toList.map Event.key) ++ t.scan.requests := by
  cases step with
  | navigate tree move _ _ _ _ => simp only [Option.toList_none, List.map_nil, List.nil_append, Scan.State.requests, ← tree, move.tree_eq]
  | read _ pending arrived => simpa only [Option.toList_some, List.map_cons, List.map_nil, Event.key, List.singleton_append, arrived] using Scan.requests_cons _ pending
  | write _ _ pending arrived => simpa only [Option.toList_some, List.map_cons, List.map_nil, Event.key, List.singleton_append, arrived] using Scan.requests_cons _ pending
  | rotate rotation => simp only [Option.toList_none, List.map_nil, List.nil_append, Scan.State.requests, ← rotation.size_eq]

theorem Trace.requests {α : Type} {s t : State α} {events : List (Event α)} {k r : Nat}
    (trace : Trace s t events k r) : s.scan.requests = events.map Event.key ++ t.scan.requests := by
  induction trace with
  | refl => rfl
  | step first _ ih => rw [first.requests, ih, List.map_append, List.append_assoc]

/-- Reads and writes consume the previously charged visit unit, so lifting the
scan introduces no hidden I/O surcharge or uncharged cell accesses. -/
theorem Trace.cost {α : Type} {s t : State α} {events : List (Event α)} {k r : Nat}
    (trace : Trace s t events k r) (valid : s.scan.Valid) : k ≤ 4 * s.scan.tree.size + 3 * r := trace.scan.cost valid

end RotationBST.TreeBuffer.Cells
