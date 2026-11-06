module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Maintenance.Correctness
public import RotationBST.Models.Labelled.Metadata.Pointer

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes
open LabelledCursor

/-- The routing projection executes exactly the already verified maintenance
program, with the same word and pointer costs. -/
theorem maintain_routing {α : Type} (side : IntervalMetadata.Maintenance.Side) (s : State α) :
    (maintain side s).map State.routing = IntervalMetadata.Maintenance.maintain side s.routing := by
  rcases s with ⟨⟨focus, cs⟩, child, parent⟩
  cases focus with
  | nil => cases side <;> rfl
  | node l entry r =>
    cases cs with
    | nil => cases side <;> rfl
    | cons frame cs => cases frame <;> cases side <;> rfl

/-- Both scratch records are overwritten before use, so callers may start the
controller with any fixed scratch values. -/
theorem maintain_scratch {α : Type} (side : IntervalMetadata.Maintenance.Side)
    (s : State α) (child parent : Nat × IntervalMetadata.Bounds) :
    maintain side ⟨s.cursor, child, parent⟩ = maintain side s := by
  rcases s with ⟨⟨focus, cs⟩, oldChild, oldParent⟩
  cases focus with
  | nil => cases side <;> rfl
  | node l entry r =>
    cases cs with
    | nil => cases side <;> rfl
    | cons frame cs => cases frame <;> cases side <;> rfl

/-- Forgetting the routing words leaves precisely a payload-preserving physical
rotation. None of the saved cell contents is overwritten or moved between keys. -/
theorem maintain_payload {α : Type} (side : IntervalMetadata.Maintenance.Side) (s : State α) :
    (maintain side s).map (fun t => t.cursor.map Entry.payload) =
      perform side.opcode (s.cursor.map Entry.payload) := by
  rcases s with ⟨⟨focus, cs⟩, child, parent⟩
  cases focus with
  | nil => cases side <;> rfl
  | node l entry r =>
    cases cs with
    | nil => cases side <;> rfl
    | cons frame cs => cases frame <;> cases side <;> rfl

theorem maintain_preserves {α : Type} (side : IntervalMetadata.Maintenance.Side)
    (data : Nat → α) {s t : State α} (execution : maintain side s = some t)
    (routing : Routing s.cursor) (stored : Stored data s.cursor) :
    Routing t.cursor ∧ Stored data t.cursor ∧ Pointer.Trace s.cursor.erase t.cursor.erase 5 := by
  have routeRun : IntervalMetadata.Maintenance.maintain side s.routing = some t.routing := by
    simpa only [execution, Option.map_some] using (maintain_routing side s).symm
  have payloadRun : perform side.opcode (s.cursor.map Entry.payload) = some (t.cursor.map Entry.payload) := by
    simpa only [execution, Option.map_some] using (maintain_payload side s).symm
  refine ⟨IntervalMetadata.Maintenance.maintain_canonical side routeRun routing, ?_, ?_⟩
  · have preserved := Metadata.perform_label data payloadRun (by simpa only [Stored, map_erase] using stored)
    simpa only [Stored, map_erase] using preserved
  · simpa only [State.routing, map_erase] using IntervalMetadata.Maintenance.maintain_physical side routeRun

theorem maintain_rotation {α : Type} (side : IntervalMetadata.Maintenance.Side) {s t : State α}
    (execution : maintain side s = some t) : Rotate s.cursor.erase.tree t.cursor.erase.tree := by
  have routeRun : IntervalMetadata.Maintenance.maintain side s.routing = some t.routing := by
    simpa only [execution, Option.map_some] using (maintain_routing side s).symm
  have rotation := IntervalMetadata.Maintenance.update_rotation
    (IntervalMetadata.Maintenance.maintain_update side routeRun)
  simpa only [State.routing, erase_tree, map_erase] using rotation

/-- A legal rotation is always implemented, including when nodes also contain
snapshot payloads. Its cost remains fifteen independently of cell contents. -/
theorem implement {α : Type} (side : IntervalMetadata.Maintenance.Side) (data : Nat → α)
    (s : State α) (target : Pointer.Config)
    (legal : Multifinger.perform side.opcode s.cursor.erase = some target)
    (routing : Routing s.cursor) (stored : Stored data s.cursor) :
    ∃ t, maintain side s = some t ∧ t.cursor.erase = target ∧ Routing t.cursor ∧ Stored data t.cursor ∧
      IntervalMetadata.Maintenance.charge (IntervalMetadata.Maintenance.program side) = 15 ∧
      Pointer.Trace s.cursor.erase t.cursor.erase 5 := by
  obtain ⟨next, run, shape, _, _, _⟩ := IntervalMetadata.Maintenance.implement side s.routing target
    (by simpa only [State.routing, map_erase] using legal) routing
  have mapped := maintain_routing side s
  rw [run] at mapped
  obtain ⟨t, execution, projection⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨fields, cells, trace⟩ := maintain_preserves side data execution routing stored
  refine ⟨t, execution, ?_, fields, cells, IntervalMetadata.Maintenance.program_charge side, trace⟩
  simpa only [← projection, State.routing, map_erase] using shape

end RotationBST.TreeBuffer.Nodes
