module

public import RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Transfers
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.CellIO
open Multifinger

private theorem undo_append (xs ys : List Opcode) : undo (xs ++ ys) = undo ys ++ undo xs := by
  simp only [undo, List.reverse_append, List.flatMap_append]

theorem inverseCells_reverse (codes : List Nat) :
    inverseCells codes.reverse = undo (decodeCells codes) := by
  induction codes with
  | nil => rfl
  | cons code codes ih =>
    have decode : decodeCells (code :: codes) = decodeCell code ++ decodeCells codes := rfl
    simpa only [List.reverse_cons, inverseCells, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, decode, undo_append] using
      congrArg (fun ops => ops ++ undo (decodeCell code)) ih

theorem inverseCells_encoded (saved : Tree) :
    inverseCells (encodedCells saved).reverse = undo (record saved) := by
  rw [inverseCells_reverse, decodeCells_encoded]

/-- A reverse buffer scan supplies the exact inverse instruction stream, with
linear read/navigation work and a linear number of emitted pointer opcodes.
Execution of those opcodes is not yet interleaved with these reads. -/
theorem read_reverse (saved current : Tree) (same : current.size = saved.size)
    (position : Nat) (present : position < current.size) (data : Nat → Nat)
    (stored : Stored saved data) :
    ∃ t events work, Cells.Trace ⟨⟨current, position, current.size, true⟩, data⟩ ⟨t, data⟩ events work 0 ∧
      t.requests = [] ∧ work ≤ 4 * current.size ∧
      events.map Cells.Event.value = (encodedCells saved).reverse ∧
      inverseCells (events.map Cells.Event.value) = undo (record saved) ∧
      (inverseCells (events.map Cells.Event.value)).length ≤ 12 * saved.size := by
  obtain ⟨t, work, run, done, bound⟩ := Cells.read_all_reverse current position present data
  have values : ((List.range current.size).reverse.map fun x => Cells.Event.read x (data x)).map Cells.Event.value =
      (encodedCells saved).reverse := by
    simp only [List.map_map, Function.comp_def, Cells.Event.value, List.map_reverse, same,
      stored_values saved data stored]
  refine ⟨t, _, work, run, done, bound, values, ?_, ?_⟩
  · rw [values, inverseCells_encoded]
  · rw [values, inverseCells_encoded]
    have inverse := undo_length (record saved)
    have length := record_length saved
    omega

/-- The stream obtained from descending cells restores the saved tree from
the common vine, preserving any ancestor context. -/
theorem reverse_replay (saved : Tree) (cs : List Pointer.Frame) :
    replay (inverseCells (encodedCells saved).reverse) ⟨vine saved.size, cs⟩ = some ⟨saved, cs⟩ := by
  rw [inverseCells_encoded]
  exact undo_replay (record_replay saved cs)

end RotationBST.TreeBuffer.Snapshot.CellIO
