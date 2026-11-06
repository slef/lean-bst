module

public import RotationBST.Structures.TreeBuffer.Snapshot.Startup.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Nodes.Initialization.Execution
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Load
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Refinement.Save

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Startup

private theorem ready_valid (tree : Tree) (data : Nat → Nat) (nonempty : tree ≠ .nil) :
    (Shared.State.mk (Nodes.label data tree 0) (fun _ : Fin 2 => Streaming.rootPosition tree)).Valid data := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Nodes.label_routing, Nodes.label_erase]
  · simp only [Nodes.label_payload, Nodes.label_erase]
  · intro i
    simpa only [Nodes.label_erase] using Streaming.rootPosition_valid tree nonempty

/-- Loading from arbitrary initial routing words includes their actual local
initialization. Existing snapshot cells survive setup and the complete load. -/
theorem load (saved current : Tree) (n : Nat) (size : n = current.size)
    (nonempty : current ≠ .nil) (same : current.size = saved.size)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → Nat) (stored : CellIO.Stored saved data) :
    ∃ final events total, Execution current n fields data final events total ∧ final.Valid data ∧
      final.tree.erase = saved ∧ (Pointer.Config.mk saved []).key? = some (final.position 0) ∧
      Streaming.Refinement.Reads data events ∧ total ≤ 848 * n := by
  obtain ⟨ready, setupCost, computed, setup, halt, cursor, _, setupBound⟩ :=
    Nodes.Initialization.complete current n size fields data
  let actual : Shared.State Nat 2 := ⟨Nodes.label data current 0, fun _ => Streaming.rootPosition current⟩
  have root : (Pointer.Config.mk current []).key? = some (actual.position 0) := by
    cases current with
    | nil => exact False.elim (nonempty rfl)
    | node l r => rfl
  obtain ⟨final, events, work, run, valid, output, finalRoot, reads, bound⟩ :=
    Streaming.Refinement.load saved current nonempty same data stored actual
      (ready_valid current data nonempty) (Nodes.label_erase data current 0) root rfl
  refine ⟨final, events, setupCost + work, ?_, valid, output, finalRoot, reads, by omega⟩
  refine ⟨ready, setupCost, work, computed, setup, halt, ?_, ?_, rfl⟩
  · rw [cursor]
  · simpa only [cursor, LabelledCursor.Config.tree, LabelledCursor.plug] using run

/-- Save over arbitrary initial cells and routing words, returning to the
original shape with a valid snapshot. Setup is included in the bound. -/
theorem save (tree : Tree) (n : Nat) (size : n = tree.size) (nonempty : tree ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → Nat) :
    ∃ final finalData events total, Execution tree n fields data final events total ∧ final.Valid finalData ∧
      CellIO.Stored tree finalData ∧ final.tree.erase = tree ∧
      (Pointer.Config.mk tree []).key? = some (final.position 0) ∧ total ≤ 1088 * n := by
  obtain ⟨ready, setupCost, computed, setup, halt, cursor, _, setupBound⟩ :=
    Nodes.Initialization.complete tree n size fields data
  let actual : Shared.State Nat 2 := ⟨Nodes.label data tree 0, fun _ => Streaming.rootPosition tree⟩
  have root : (Pointer.Config.mk tree []).key? = some (actual.position 0) := by
    cases tree with
    | nil => exact False.elim (nonempty rfl)
    | node l r => rfl
  obtain ⟨final, finalData, events, work, run, valid, stored, output, finalRoot, bound⟩ :=
    Recording.Refinement.save tree data nonempty actual (ready_valid tree data nonempty)
      (Nodes.label_erase data tree 0) root rfl
  refine ⟨final, finalData, events, setupCost + work, ?_, valid, stored, output, finalRoot, by omega⟩
  refine ⟨ready, setupCost, work, computed, setup, halt, ?_, ?_, rfl⟩
  · rw [cursor]
  · simpa only [cursor, LabelledCursor.Config.tree, LabelledCursor.plug] using run

end RotationBST.TreeBuffer.Snapshot.Startup
