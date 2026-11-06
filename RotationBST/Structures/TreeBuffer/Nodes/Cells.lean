module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Models.Labelled.Metadata.Write

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes
open LabelledCursor

theorem read_value {α : Type} (data : Nat → α) (c : Config (Entry α)) (entry : Entry α)
    (read : c.read = some entry) (stored : Stored data c) : entry.cell = data entry.key := by
  have projected : (c.map Entry.payload).read = some (entry.key, entry.cell) := by
    simp only [map_read, read, Option.map_some, Entry.payload]
  have atNode := Metadata.cursor_read projected
  rw [stored] at atNode
  exact Metadata.at_payload data c.erase.tree 0 entry.key entry.cell atNode

/-- Reading a represented node returns its saved cell value for one word access. -/
theorem read_correct {α : Type} (data : Nat → α) (c : Config (Entry α)) (entry : Entry α)
    (read : c.read = some entry) (stored : Stored data c) : readCell c = some (1, data entry.key) := by
  simp only [readCell, read, Option.map_some, read_value data c entry read stored]

theorem write_routing {α : Type} (c : Config (Entry α)) (value : α) :
    (writeCell c value).map (fun result => result.2.map Entry.routing) =
      c.read.map (fun _ => c.map Entry.routing) := by
  rcases c with ⟨focus, cs⟩
  cases focus <;> rfl

theorem write_payload {α : Type} (c : Config (Entry α)) (entry : Entry α) (value : α)
    (read : c.read = some entry) :
    (writeCell c value).map (fun result => result.2.map Entry.payload) =
      (c.map Entry.payload).write (entry.key, value) := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => simp [Config.read] at read
  | node l e r => cases Option.some.inj read; rfl

theorem write_shape {α : Type} {c next : Config (Entry α)} {value : α} {cost : Nat}
    (execution : writeCell c value = some (cost, next)) : next.erase = c.erase := by
  rcases c with ⟨focus, cs⟩
  cases focus <;> simp only [writeCell, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at execution
  obtain ⟨rfl, rfl⟩ := execution
  rfl

/-- Writing one cell preserves all routing fields and realizes precisely the
key-indexed update used by the buffer event model. -/
theorem write_correct {α : Type} (data : Nat → α) (c : Config (Entry α)) (entry : Entry α) (value : α)
    (read : c.read = some entry) (routing : Routing c) (stored : Stored data c) :
    ∃ next, writeCell c value = some (1, next) ∧ next.erase = c.erase ∧ Routing next ∧
      Stored (Function.update data entry.key value) next := by
  have available : ∃ next, writeCell c value = some (1, next) := by
    rcases c with ⟨focus, cs⟩
    cases focus with
    | nil => simp [Config.read] at read
    | node l e r => exact ⟨_, rfl⟩
  obtain ⟨next, execution⟩ := available
  have fields : next.map Entry.routing = c.map Entry.routing := by
    simpa only [execution, read, Option.map_some, Option.some.injEq] using write_routing c value
  have shape : next.erase = c.erase := by
    simpa only [map_erase] using congrArg Config.erase fields
  refine ⟨next, execution, shape, ?_, ?_⟩
  · simpa only [Routing, fields] using routing
  · have readPayload : (c.map Entry.payload).read = some (entry.key, entry.cell) := by
      simp only [map_read, read, Option.map_some, Entry.payload]
    have writePayload : (c.map Entry.payload).write (entry.key, value) = some (next.map Entry.payload) := by
      simpa only [execution, Option.map_some] using (write_payload c entry value read).symm
    have effect := Metadata.write_result data (Metadata.cursor_write readPayload writePayload)
      (by simpa only [Stored, erase_tree, map_erase] using stored)
    simpa only [Stored, erase_tree, map_erase] using effect

end RotationBST.TreeBuffer.Nodes
