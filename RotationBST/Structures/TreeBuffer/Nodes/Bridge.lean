module

public import RotationBST.Structures.TreeBuffer.Nodes.Cells
public import RotationBST.Structures.TreeBuffer.Nodes.Routing
public import RotationBST.Structures.TreeBuffer.Nodes.Maintenance
public import RotationBST.Structures.TreeBuffer.Cells.Operational

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes
open LabelledCursor

/-- The charged route operation realizes a cell-model navigation step without
altering any payload or routing invariant. -/
theorem navigate_step {α : Type} (s : Cells.State α) (valid : s.scan.Valid) (pending : s.scan.requests ≠ [])
    (c : Config (Entry α)) (entry : Entry α) (read : c.read = some entry)
    (tree : c.erase.tree = s.scan.tree) (key : entry.key = s.scan.position)
    (routing : Routing c) (stored : Stored s.data c) (different : s.scan.position ≠ s.scan.target) :
    ∃ next position, route s.scan.target c = some (4, next) ∧
      Cells.Step s ⟨{ s.scan with tree := next.erase.tree, position := position }, s.data⟩ none 1 0 ∧
      Routing next ∧ Stored s.data next := by
  obtain ⟨next, position, execution, physical, atKey, closer, fields, cells⟩ :=
    progress s.data s.scan.target c entry read routing stored
      (by rw [tree]; exact Scan.target_valid s.scan valid pending) (by simpa only [key] using different)
  have view := IntervalMetadata.Access.read_valid (c.map Entry.routing) routing entry.key entry.bounds
    (by simp only [map_read, read, Option.map_some, Entry.routing])
  have current : c.erase.key? = some s.scan.position := by simpa only [map_erase, key] using view.2.1
  exact ⟨next, position, execution,
    .navigate tree physical current atKey pending (by simpa only [tree, key] using closer), fields, cells⟩

/-- A buffer read event is backed by the actual one-word node read. -/
theorem read_step {α : Type} (s : Cells.State α) (valid : s.scan.Valid) (pending : s.scan.requests ≠ [])
    (c : Config (Entry α)) (entry : Entry α) (read : c.read = some entry)
    (key : entry.key = s.scan.position) (stored : Stored s.data c) (arrived : s.scan.position = s.scan.target) :
    readCell c = some (1, s.data s.scan.position) ∧
      Cells.Step s ⟨s.scan.afterVisit, s.data⟩
        (some (.read s.scan.position (s.data s.scan.position))) 1 0 := by
  exact ⟨by simpa only [key] using read_correct s.data c entry read stored, .read valid.1 pending arrived⟩

/-- A buffer write event updates one cell and leaves its routing annotation
valid, ready for the next scan move or rotation. -/
theorem write_step {α : Type} (s : Cells.State α) (valid : s.scan.Valid) (pending : s.scan.requests ≠ [])
    (c : Config (Entry α)) (entry : Entry α) (value : α) (read : c.read = some entry)
    (key : entry.key = s.scan.position) (routing : Routing c) (stored : Stored s.data c)
    (arrived : s.scan.position = s.scan.target) :
    ∃ next, writeCell c value = some (1, next) ∧ next.erase = c.erase ∧ Routing next ∧
      Stored (Function.update s.data s.scan.position value) next ∧
      Cells.Step s ⟨s.scan.afterVisit, Function.update s.data s.scan.position value⟩
        (some (.write s.scan.position value)) 1 0 := by
  obtain ⟨next, execution, shape, fields, cells⟩ := write_correct s.data c entry value read routing stored
  exact ⟨next, execution, shape, fields, by simpa only [key] using cells, .write value valid.1 pending arrived⟩

/-- A charged maintenance call realizes an external rotation of the cell
model. The scan finger's key remains fixed while the shared shape changes. -/
theorem rotation_step {α : Type} (side : IntervalMetadata.Maintenance.Side) (s : Cells.State α)
    {before after : State α} (execution : maintain side before = some after)
    (tree : before.cursor.erase.tree = s.scan.tree)
    (routing : Routing before.cursor) (stored : Stored s.data before.cursor) :
    Cells.Step s ⟨{ s.scan with tree := after.cursor.erase.tree }, s.data⟩ none 0 1 ∧
      Routing after.cursor ∧ Stored s.data after.cursor ∧
      IntervalMetadata.Maintenance.charge (IntervalMetadata.Maintenance.program side) = 15 := by
  have rotation := maintain_rotation side execution
  rw [tree] at rotation
  obtain ⟨fields, cells, _⟩ := maintain_preserves side s.data execution routing stored
  exact ⟨.rotate rotation, fields, cells, IntervalMetadata.Maintenance.program_charge side⟩

end RotationBST.TreeBuffer.Nodes
