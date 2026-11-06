module

public import RotationBST.Structures.TreeBuffer.Cells.Next
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

theorem effect_append {α : Type} (data : Nat → α) (first last : List (Event α)) :
    effect data (first ++ last) = effect (effect data first) last := by
  induction first generalizing data with
  | nil => rfl
  | cons event events ih => cases event <;> exact ih _

theorem Step.effect {α : Type} {s t : State α} {event : Option (Event α)} {w r : Nat}
    (step : Step s t event w r) : t.data = effect s.data event.toList := by cases step <;> rfl

theorem Trace.effect {α : Type} {s t : State α} {events : List (Event α)} {w r : Nat}
    (trace : Trace s t events w r) : t.data = effect s.data events := by
  induction trace with
  | refl => rfl
  | step first _ ih => rw [effect_append, ← first.effect]; exact ih

theorem effect_writes {α : Type} (data target : Nat → α) (keys : List Nat) :
    effect data (keys.map fun x => Event.write x (target x)) = writeMany target keys data := by
  induction keys generalizing data with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem Trace.writes {α : Type} {s t : State α} {target : Nat → α} {keys : List Nat} {w r : Nat}
    (trace : Trace s t (keys.map fun x => Event.write x (target x)) w r) (x : Nat) :
    t.data x = if x ∈ keys then target x else s.data x := by
  rw [trace.effect, effect_writes, writeMany_apply]

theorem Trace.append {α : Type} {s t u : State α} {first last : List (Event α)} {w r v q : Nat}
    (left : Trace s t first w r) (right : Trace t u last v q) :
    Trace s u (first ++ last) (w + v) (r + q) := by
  induction left with
  | refl => simpa using right
  | step first _ ih => simpa only [List.append_assoc, Nat.add_assoc] using Trace.step first (ih right)

/-- A scan with no work performs no cell accesses, even if it rotates. -/
theorem rotations_only {α : Type} {s t : Scan.State} {r : Nat} (scan : Scan.Trace s t 0 r)
    (valid : s.Valid) (data : Nat → α) : Trace ⟨s, data⟩ ⟨t, data⟩ [] 0 r := by
  obtain ⟨keys, run, sequence⟩ := lift_read scan valid data
  have visits := scan.visits_le
  rw [sequence, List.length_append] at visits
  have empty : keys = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa only [empty, List.map_nil] using run

theorem scan_fixed {s t : Scan.State} {w r : Nat} (scan : Scan.Trace s t w r) (zero : r = 0) :
    s.tree = t.tree := by
  induction scan with
  | refl => rfl
  | @step s t u w r v q first rest ih =>
    have next := ih (by omega)
    cases first with
    | move tree move _ _ _ _ => exact (tree.symm.trans move.tree_eq).trans next
    | visit _ _ => exact next
    | rotate _ => omega

end RotationBST.TreeBuffer.Cells
