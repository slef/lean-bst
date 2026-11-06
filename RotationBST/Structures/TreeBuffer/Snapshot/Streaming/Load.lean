module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Restoration
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming
open Multifinger

theorem rootPosition_valid (tree : Tree) (nonempty : tree ≠ .nil) : rootPosition tree < tree.size := by
  cases tree with
  | nil => exact False.elim (nonempty rfl)
  | node l r => simp [rootPosition, Pointer.Config.key?, Pointer.offset, Tree.size]; omega

/-- The normalizer preserves the inactive buffer finger's key. Its shape
updates project to the very same rotation trace, with no buffer navigation. -/
theorem normalization_scan (current : Tree) :
    ∃ rotations, Scan.Trace ⟨current, rootPosition current, current.size, true⟩
      ⟨vine current.size, rootPosition current, current.size, true⟩ 0 rotations ∧
      rotations ≤ (record current).length := by
  obtain ⟨rotations, bound, physical⟩ := (replay_trace (record_replay current [])).rotations
  exact ⟨rotations, rotations_scan physical _ rfl, bound⟩

/-- Load a stored snapshot from any same-size tree, counting normalization,
buffer navigation, node reads, and inverse replay. The local normalizer runs
without retaining its emitted log; the replay phase retains at most 12 opcodes. -/
theorem load (saved current : Tree) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) :
    ∃ cost, Load data current saved cost ∧ cost ≤ 56 * current.size := by
  have restoration : ∃ t w p r, Trace data (initial (vine current.size) (rootPosition current)) t w p r ∧
      t.Done ∧ t.cursor = ⟨saved, []⟩ ∧ p = (undo (record saved)).length ∧ w + p ≤ 52 * saved.size := by
    by_cases empty : current = .nil
    · subst current
      simpa only [same, rootPosition, Pointer.Config.key?, Option.getD_none] using restore saved data stored
    · have present : rootPosition current < saved.size := by rw [← same]; exact rootPosition_valid current empty
      simpa only [same] using restore_from saved data stored (rootPosition current) present
  obtain ⟨t, w, p, r, run, done, result, _, cost⟩ := restoration
  obtain ⟨normalRotations, scan, rotationBound⟩ := normalization_scan current
  refine ⟨(record current).length + w + p, ?_, ?_⟩
  · exact ⟨record current, normalRotations, t, w, p, r, Controller.normalization current,
      scan, rotationBound, run, done, result, rfl⟩
  · have normalization := record_length current
    omega

end RotationBST.TreeBuffer.Snapshot.Streaming
