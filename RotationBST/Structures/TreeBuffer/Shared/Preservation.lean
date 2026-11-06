module

public import RotationBST.Structures.TreeBuffer.Shared.Views
public import RotationBST.Structures.TreeBuffer.Cells.Effects
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Shared
open LabelledCursor

theorem valid_cursor {α : Type} {fingers : Nat} (c : Config (Nodes.Entry α)) (position : Fin fingers → Nat)
    (data : Nat → α) (routing : Nodes.Routing c) (stored : Nodes.Stored data c)
    (existing : ∀ i, position i < c.tree.erase.size) : (State.mk c.tree position).Valid data := by
  refine ⟨?_, ?_, existing⟩
  · simpa only [Nodes.Routing, IntervalMetadata.Access.Canonical, map_tree, LabelledTree.erase_map] using routing
  · simpa only [Nodes.Stored, map_tree, ← erase_tree] using stored

theorem key_existing {α : Type} (c : Config (Nodes.Entry α)) (entry : Nodes.Entry α)
    (routing : Nodes.Routing c) (read : c.read = some entry) : entry.key < c.tree.erase.size := by
  have fields := IntervalMetadata.Access.read_valid (c.map Nodes.Entry.routing) routing entry.key entry.bounds
    (by simp only [map_read, read, Option.map_some, Nodes.Entry.routing])
  have bound := Pointer.Config.key_lt_size (c.map Nodes.Entry.routing).erase entry.key fields.2.1
  simpa only [map_erase, erase_tree] using bound

theorem Step.size_eq {α : Type} {fingers : Nat} {s t : State α fingers} {i : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost) :
    s.tree.erase.size = t.tree.erase.size := by
  cases step with
  | move _ view execution move _ => simp only [move_tree execution move, view.1]
  | navigate target view execution _ => simp only [Nodes.route_tree execution, view.1]
  | read _ _ => rfl
  | write _ view execution =>
    simpa only [erase_tree, ← view.1] using congrArg (fun c : Pointer.Config => c.tree.size) (Nodes.write_shape execution).symm
  | rotate side view execution =>
    simpa only [← erase_tree, view.1] using (Nodes.maintain_rotation side execution).size_eq

/-- Every inactive finger keeps its physical node identity across all shared
operations, including writes and rotations that change its local view. -/
theorem Step.inactive {α : Type} {fingers : Nat} {s t : State α fingers} {i j : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost) (different : j ≠ i) :
    t.position j = s.position j := by
  cases step <;> simp only [Function.update_of_ne different]

/-- Coherence of all fingers and both sets of node fields survives each charged
operation. Payload effects are exactly those of the observable cell event. -/
theorem Step.valid {α : Type} {fingers : Nat} {s t : State α fingers} {i : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost)
    (data : Nat → α) (valid : s.Valid data) : t.Valid (Cells.effect data event.toList) := by
  have size := step.size_eq
  cases step with
  | @move c next entry nextEntry op view execution move read =>
    obtain ⟨routing, stored⟩ := view_invariants view valid
    have fields : Nodes.Routing next := by
      simpa only [Nodes.Routing, IntervalMetadata.Access.Canonical, map_tree, move_tree execution move] using routing
    have cells : Nodes.Stored data next := by
      simpa only [Nodes.Stored, map_tree, ← erase_tree, move_tree execution move] using stored
    apply valid_cursor next _ data fields cells
    intro j
    by_cases same : j = i
    · subst j
      simpa only [Function.update_self] using key_existing next nextEntry fields read
    · simpa only [Function.update_of_ne same, ← size] using valid.2.2 j
  | @navigate c next entry nextEntry target view execution read =>
    obtain ⟨routing, stored⟩ := view_invariants view valid
    obtain ⟨_, fields, cells⟩ := Nodes.route_preserves data execution routing stored
    apply valid_cursor next _ data fields cells
    intro j
    by_cases same : j = i
    · subst j
      simpa only [Function.update_self] using key_existing next nextEntry fields read
    · simpa only [Function.update_of_ne same, ← size] using valid.2.2 j
  | read _ _ => exact valid
  | @write c next entry value view execution =>
    obtain ⟨routing, stored⟩ := view_invariants view valid
    obtain ⟨result, written, _, fields, cells⟩ := Nodes.write_correct data c entry value view.2.1 routing stored
    have same := Option.some.inj (execution.symm.trans written)
    cases (Prod.mk.inj same).2
    apply valid_cursor next _ _ fields
    · simpa only [view.2.2, Option.toList_some, Cells.effect] using cells
    · intro j
      simpa only [← size] using valid.2.2 j
  | @rotate before after entry side view execution =>
    obtain ⟨routing, stored⟩ := view_invariants view valid
    obtain ⟨fields, cells, _⟩ := Nodes.maintain_preserves side data execution routing stored
    apply valid_cursor after.cursor _ data fields cells
    intro j
    simpa only [← size] using valid.2.2 j

/-- In particular, an untouched finger has a view of the updated shared tree
at exactly its old node, with current metadata and cell contents. -/
theorem Step.inactive_view {α : Type} {fingers : Nat} {s t : State α fingers} {i j : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost)
    (data : Nat → α) (valid : s.Valid data) (different : j ≠ i) :
    ∃ c entry, View t j c entry ∧ entry.key = s.position j := by
  obtain ⟨c, entry, view⟩ := view_exists t _ (step.valid data valid) j
  exact ⟨c, entry, view, view.2.2.trans (step.inactive different)⟩

theorem Trace.valid {α : Type} {fingers : Nat} {s t : State α fingers} {events : List (Cells.Event α)}
    {cost : Nat} (trace : Trace s t events cost) (data : Nat → α) (valid : s.Valid data) :
    t.Valid (Cells.effect data events) := by
  induction trace generalizing data with
  | refl => exact valid
  | step first _ ih =>
    rw [Cells.effect_append]
    exact ih _ (first.valid data valid)

/-- A complete shared-node trace retains its finite node universe. -/
theorem Trace.size_eq {α : Type} {fingers : Nat} {s t : State α fingers} {events : List (Cells.Event α)}
    {cost : Nat} (trace : Trace s t events cost) : s.tree.erase.size = t.tree.erase.size := by
  induction trace with
  | refl => rfl
  | step first _ ih => exact first.size_eq.trans ih

end RotationBST.TreeBuffer.Shared
