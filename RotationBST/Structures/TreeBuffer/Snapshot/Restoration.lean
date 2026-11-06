module

public import RotationBST.Structures.TreeBuffer.Snapshot.Normalization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot
open Multifinger

/-- Saving may normalize temporarily, but this complete save program returns
to the exact original tree and cursor. -/
theorem save_replay (t : Tree) (cs : List Pointer.Frame) :
    replay (saveProgram t) ⟨t, cs⟩ = some ⟨t, cs⟩ :=
  replay_roundtrip (record_replay t cs)

theorem save_length (t : Tree) : (saveProgram t).length ≤ 16 * t.size := by
  have first := record_length t
  have last := undo_length (record t)
  simp only [saveProgram, List.length_append]
  omega

/-- Restoration uses the current tree and the saved opcode list alone. Equal
sizes ensure that both normalization passes have the same canonical endpoint. -/
theorem load_replay (current saved : Tree) (same : current.size = saved.size) (cs : List Pointer.Frame) :
    replay (loadProgram current (record saved)) ⟨current, cs⟩ = some ⟨saved, cs⟩ := by
  rw [loadProgram, replay_append, record_replay, Option.bind_some, same]
  exact undo_replay (record_replay saved cs)

theorem load_length (current saved : Tree) (same : current.size = saved.size) :
    (loadProgram current (record saved)).length ≤ 16 * current.size := by
  have first := record_length current
  have savedLength := record_length saved
  have last := undo_length (record saved)
  simp only [loadProgram, List.length_append]
  omega

/-- The recorded opcodes retain the entire tree shape, not merely its size. -/
theorem record_injective (s t : Tree) (same : s.size = t.size) (logs : record s = record t) : s = t := by
  have left := undo_replay (record_replay s [])
  have right := undo_replay (record_replay t [])
  rw [same, logs, right] at left
  exact (congrArg Pointer.Config.focus (Option.some.inj left)).symm

theorem save_trace (t : Tree) : Pointer.Trace ⟨t, []⟩ ⟨t, []⟩ (saveProgram t).length :=
  replay_trace (save_replay t [])

theorem load_trace (current saved : Tree) (same : current.size = saved.size) :
    Pointer.Trace ⟨current, []⟩ ⟨saved, []⟩ (loadProgram current (record saved)).length :=
  replay_trace (load_replay current saved same [])

end RotationBST.TreeBuffer.Snapshot
