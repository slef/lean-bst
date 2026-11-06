module

public import RotationBST.Structures.TreeBuffer.Shared.Erasure.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Execution
public import RotationBST.Models.Multifinger.Proofs

@[expose] public section
namespace RotationBST.TreeBuffer.Shared
open LabelledCursor

private theorem route_move {α : Type} {target cost : Nat} {c next : Config (Nodes.Entry α)}
    {entry : Nodes.Entry α} (read : c.read = some entry) (run : Nodes.route target c = some (cost, next)) :
    Pointer.Move c.erase next.erase := by
  have projected : IntervalMetadata.Access.route target (c.map Nodes.Entry.routing) = some (cost, next.map Nodes.Entry.routing) := by
    simpa only [run, Option.map_some] using (Nodes.route_routing target c).symm
  have erased := IntervalMetadata.Access.route_erase target (c.map Nodes.Entry.routing) entry.key entry.bounds
    (by simp only [map_read, read, Option.map_some, Nodes.Entry.routing])
  simp only [projected, Option.map_some, map_erase] at erased
  obtain ⟨direction, _, physical⟩ := Option.bind_eq_some_iff.mp erased.symm
  exact Pointer.Routing.perform_sound physical

private theorem maintain_erase {α : Type} (side : IntervalMetadata.Maintenance.Side) {before after : Nodes.State α}
    (run : Nodes.maintain side before = some after) :
    Multifinger.perform side.opcode before.cursor.erase = some after.cursor.erase := by
  have physical : perform side.opcode (before.cursor.map Nodes.Entry.payload) = some (after.cursor.map Nodes.Entry.payload) := by
    simpa only [run, Option.map_some] using (Nodes.maintain_payload side before).symm
  have erased := perform_erase side.opcode (before.cursor.map Nodes.Entry.payload)
  simpa only [physical, Option.map_some, map_erase] using erased.symm

private theorem rotation_key (side : IntervalMetadata.Maintenance.Side) (a b : Pointer.Config)
    (run : Multifinger.perform side.opcode a = some b) : b.key? = a.key? := by
  rcases a with ⟨focus, context⟩
  cases side <;> cases focus <;> cases context <;> simp [IntervalMetadata.Maintenance.Side.opcode, Multifinger.perform] at run
  all_goals rename_i frame rest; cases frame <;> simp at run
  all_goals subst b; simp [Pointer.Config.key?, Pointer.offset, Tree.size, Nat.add_assoc]

/-- A shared operation erases to one legal multifinger instruction or a
stationary state. Its instruction charge is no larger than the shared charge. -/
theorem Step.erase {α : Type} {fingers : Nat} {s t : State α fingers} {i : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost)
    (data : Nat → α) (valid : s.Valid data) :
    ∃ touches, Multifinger.Trace s.erase touches t.erase ∧ touches.length ≤ cost := by
  cases step with
  | @move c next entry nextEntry op view run move read =>
    have afterValid := (Step.move op view run move read).valid data valid
    have key : next.erase.key? = some nextEntry.key := by
      simpa only [Function.update_self] using view_key
        (show View ⟨next.tree, Function.update s.position i nextEntry.key⟩ i next nextEntry from
          ⟨rfl, read, by simp⟩) afterValid
    refine ⟨[nextEntry.key], ?_, by simp⟩
    have physical : Multifinger.Step s.erase i ⟨next.erase.tree, Function.update s.position i nextEntry.key⟩ :=
      .execute (by simp only [State.erase, ← erase_tree, view.1]) (view_key view valid) move.step key
    simpa only [State.erase, erase_tree, Function.update_self] using Multifinger.Trace.step physical Multifinger.Trace.refl
  | @navigate c next entry nextEntry target view run read =>
    have move := route_move view.2.1 run
    have afterValid := (Step.navigate target view run read).valid data valid
    have key : next.erase.key? = some nextEntry.key := by
      simpa only [Function.update_self] using view_key
        (show View ⟨next.tree, Function.update s.position i nextEntry.key⟩ i next nextEntry from
          ⟨rfl, read, by simp⟩) afterValid
    refine ⟨[nextEntry.key], ?_, by simp⟩
    have physical : Multifinger.Step s.erase i ⟨next.erase.tree, Function.update s.position i nextEntry.key⟩ :=
      .execute (by simp only [State.erase, ← erase_tree, view.1]) (view_key view valid) move.step key
    simpa only [State.erase, erase_tree, Function.update_self] using Multifinger.Trace.step physical Multifinger.Trace.refl
  | read _ _ => exact ⟨[], .refl, by decide⟩
  | @write c next entry value view run =>
    have same : (State.mk next.tree s.position).erase = s.erase := by
      have shape := congrArg Pointer.Config.tree (Nodes.write_shape run)
      simp only [State.erase]
      congr 1
      simpa only [← erase_tree, view.1] using shape
    exact ⟨[], by rw [same]; exact .refl, by decide⟩
  | @rotate before after entry side view run =>
    have operation := maintain_erase side run
    have key : after.cursor.erase.key? = some (s.position i) := (rotation_key side _ _ operation).trans (view_key view valid)
    have physical : Multifinger.Step s.erase i ⟨after.cursor.erase.tree, Function.update s.position i (s.position i)⟩ :=
      .execute (by simp only [State.erase, ← erase_tree, view.1]) (view_key view valid) (Multifinger.perform_sound operation) key
    refine ⟨[s.position i], ?_, by simp⟩
    simpa only [State.erase, erase_tree, Function.update_eq_self] using Multifinger.Trace.step physical Multifinger.Trace.refl

end RotationBST.TreeBuffer.Shared
