module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Refinement.Traces
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Snapshot
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Traces

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording.Refinement

/-- Compose recording and restoration at their actual shared cursor positions.
The only phase change resets scalar scan control; it does not move a finger. -/
theorem save_execution_bounded (tree : Tree) (data finalData : Nat → Nat) (modelCost : Nat)
    (run : Save data tree finalData modelCost) (nonempty : tree ≠ .nil)
    (actual : Shared.State Nat 2) (represented : Represents actual (initial tree data)) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid finalData ∧
      final.tree.erase = tree ∧ (Pointer.Config.mk tree []).key? = some (final.position 0) ∧
      cost ≤ 15 * modelCost ∧
      (∀ key value, Cells.Event.write key value ∈ events → value < 2 ^ 12) := by
  obtain ⟨recorded, ops, work, rotations, restored, reads, instructions, replayRotations,
    recording, phaseRoot, restoration, done, output, finalDataEq, total⟩ := run
  subst finalData
  have initialValid := initial_valid tree data nonempty
  obtain ⟨middle, writeEvents, recordCost, actualRecord, recordRep, recordBound, written⟩ :=
    trace_bounded recording initialValid actual represented
  have recordedValid := recording.valid initialValid
  have replayRep : Streaming.Refinement.Represents middle
      (Streaming.initial recorded.scan.tree recorded.scan.position) recorded.data := by
    refine ⟨recordRep.1, ?_, ?_, recordRep.2.2.2⟩
    · simpa only [phaseRoot, Streaming.initial] using recordRep.2.1
    · simpa only [phaseRoot, Streaming.initial] using recordRep.2.2.1
  have replayValid := Streaming.initial_valid recorded.scan.tree recorded.scan.position recordedValid.2.1
  obtain ⟨final, readEvents, replayCost, actualReplay, finalRep, readOnly, replayBound⟩ :=
    Streaming.Refinement.trace restoration replayValid middle replayRep
  refine ⟨final, writeEvents ++ readEvents, recordCost + replayCost, actualRecord.append actualReplay,
    finalRep.1, ?_, ?_, ?_, ?_⟩
  · simpa only [output, Pointer.Config.tree, Pointer.plug] using finalRep.2.1
  · simpa only [output] using finalRep.2.2.1
  · omega
  · intro key value member
    rcases List.mem_append.mp member with stored | read
    · exact written key value stored
    · obtain ⟨_, impossible⟩ := readOnly (.write key value) read
      cases impossible

theorem save_execution (tree : Tree) (data finalData : Nat → Nat) (modelCost : Nat)
    (run : Save data tree finalData modelCost) (nonempty : tree ≠ .nil)
    (actual : Shared.State Nat 2) (represented : Represents actual (initial tree data)) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ final.Valid finalData ∧
      final.tree.erase = tree ∧ (Pointer.Config.mk tree []).key? = some (final.position 0) ∧
      cost ≤ 15 * modelCost := by
  obtain ⟨final, events, cost, execution, valid, shape, root, bound, _⟩ :=
    save_execution_bounded tree data finalData modelCost run nonempty actual represented
  exact ⟨final, events, cost, execution, valid, shape, root, bound⟩

/-- A complete nonempty shape-preserving save on the shared-node machine. It
stores the encoded snapshot and charges normalization, writes, routing reads,
rotation maintenance, and inverse replay. Initial field setup is separate. -/
theorem save_bounded (tree : Tree) (data : Nat → Nat) (nonempty : tree ≠ .nil) (actual : Shared.State Nat 2)
    (valid : actual.Valid data) (shape : actual.tree.erase = tree)
    (root : (Pointer.Config.mk tree []).key? = some (actual.position 0))
    (buffer : actual.position 1 = Streaming.rootPosition tree) :
    ∃ final finalData events cost, Shared.Trace actual final events cost ∧ final.Valid finalData ∧
      CellIO.Stored tree finalData ∧ final.tree.erase = tree ∧
      (Pointer.Config.mk tree []).key? = some (final.position 0) ∧ cost ≤ 1080 * tree.size ∧
      (∀ key value, Cells.Event.write key value ∈ events → value < 2 ^ 12) := by
  obtain ⟨finalData, modelCost, run, stored, bound⟩ := Recording.save tree data
  have represented : Represents actual (initial tree data) := ⟨valid, shape, root, buffer⟩
  obtain ⟨final, events, cost, execution, finalValid, output, finalRoot, charged, written⟩ :=
    save_execution_bounded tree data finalData modelCost run nonempty actual represented
  exact ⟨final, finalData, events, cost, execution, finalValid, stored, output, finalRoot, by omega, written⟩

theorem save (tree : Tree) (data : Nat → Nat) (nonempty : tree ≠ .nil) (actual : Shared.State Nat 2)
    (valid : actual.Valid data) (shape : actual.tree.erase = tree)
    (root : (Pointer.Config.mk tree []).key? = some (actual.position 0))
    (buffer : actual.position 1 = Streaming.rootPosition tree) :
    ∃ final finalData events cost, Shared.Trace actual final events cost ∧ final.Valid finalData ∧
      CellIO.Stored tree finalData ∧ final.tree.erase = tree ∧
      (Pointer.Config.mk tree []).key? = some (final.position 0) ∧ cost ≤ 1080 * tree.size := by
  obtain ⟨final, finalData, events, cost, execution, finalValid, stored, output, finalRoot, bound, _⟩ :=
    save_bounded tree data nonempty actual valid shape root buffer
  exact ⟨final, finalData, events, cost, execution, finalValid, stored, output, finalRoot, bound⟩

end RotationBST.TreeBuffer.Snapshot.Recording.Refinement
