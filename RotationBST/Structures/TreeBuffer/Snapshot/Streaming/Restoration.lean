module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Completion
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming
open Multifinger

theorem initial_valid (tree : Tree) (position : Nat) (present : position < tree.size) :
    (initial tree position).Valid := ⟨rfl, ⟨present, Nat.le_refl _⟩, Nat.zero_le _⟩

theorem initial_remaining (saved current : Tree) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) (position : Nat) :
    remaining data (initial current position) = undo (record saved) := by
  simp only [remaining, initial, List.nil_append, Scan.State.requests, ↓reduceIte,
    List.map_reverse, same, CellIO.stored_values saved data stored, CellIO.inverseCells_encoded]

theorem initial_potential (saved current : Tree) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) (position : Nat)
    (present : position < current.size) :
    potential data (initial current position) ≤ 52 * saved.size := by
  have scan := Scan.potential_le (initial current position).scan (initial_valid current position present).2.1
  have inverse := undo_length (record saved)
  have length := record_length saved
  rw [potential, initial_remaining saved current same data stored position]
  change Scan.potential (initial current position).scan ≤ 4 * current.size at scan
  omega

/-- The packet and scan counters remain bounded at every execution prefix.
No list of previously read cells or previously executed opcodes is retained. -/
theorem Trace.space {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (valid : s.Valid) :
    t.packet.length ≤ 12 ∧ t.scan.next ≤ s.scan.tree.size ∧ t.scan.position < s.scan.tree.size := by
  have next := trace.valid valid
  have same := trace.scan.size_eq
  exact ⟨next.2.2, by simpa only [same] using next.2.1.2, by simpa only [same] using next.2.1.1⟩

/-- Restore a nonempty saved tree by interleaving cell reads and individual
inverse instructions. The bound counts buffer navigation, reads, and replay
instructions together. Data remains attached to keys throughout the run. -/
theorem restore_from (saved : Tree) (data : Nat → Nat) (stored : CellIO.Stored saved data)
    (position : Nat) (present : position < saved.size) :
    ∃ t w p r, Trace data (initial (vine saved.size) position) t w p r ∧
      t.Done ∧ t.cursor = ⟨saved, []⟩ ∧ p = (undo (record saved)).length ∧ w + p ≤ 52 * saved.size := by
  have size := vine_size saved.size
  have valid := initial_valid (vine saved.size) position (by simpa only [size] using present)
  have stream := initial_remaining saved (vine saved.size) size data stored position
  have executable : replay (remaining data (initial (vine saved.size) position))
      (initial (vine saved.size) position).cursor = some ⟨saved, []⟩ := by
    rw [stream]
    exact undo_replay (record_replay saved [])
  obtain ⟨t, w, p, r, run, done, cost⟩ := finish data _ valid ⟨saved, []⟩ executable
  have output := completed run done
  have cursor : t.cursor = ⟨saved, []⟩ := Option.some.inj (output.1.symm.trans executable)
  have bound := initial_potential saved (vine saved.size) size data stored position (by simpa only [size] using present)
  exact ⟨t, w, p, r, run, done, cursor, by simpa only [stream] using output.2, by omega⟩

/-- Whole-tree streaming restoration, including the empty snapshot. In a
nonempty vine the initial buffer key zero is also the root key. -/
theorem restore (saved : Tree) (data : Nat → Nat) (stored : CellIO.Stored saved data) :
    ∃ t w p r, Trace data (initial (vine saved.size) 0) t w p r ∧
      t.Done ∧ t.cursor = ⟨saved, []⟩ ∧ p = (undo (record saved)).length ∧ w + p ≤ 52 * saved.size := by
  cases saved with
  | nil => exact ⟨initial .nil 0, 0, 0, 0, .refl, ⟨rfl, rfl⟩, rfl, rfl, Nat.le_refl _⟩
  | node l r => exact restore_from (.node l r) data stored 0 (by simp [Tree.size])

end RotationBST.TreeBuffer.Snapshot.Streaming
