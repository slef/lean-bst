module

public import RotationBST.Structures.TreeBuffer.Snapshot.Restoration
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot
open Multifinger

theorem pack_length (n : Nat) (ops : List Opcode) : (pack n ops).length = n := by
  induction n generalizing ops with
  | zero => rfl
  | succ n ih => simp only [pack, List.length_cons, ih]

theorem pack_cell_bound (n : Nat) (ops : List Opcode) : ∀ cell ∈ pack n ops, cell.length ≤ 4 := by
  induction n generalizing ops with
  | zero => simp [pack]
  | succ n ih =>
    intro cell member
    simp only [pack, List.mem_cons] at member
    rcases member with rfl | rest
    · simp only [List.length_take]; exact Nat.min_le_left _ _
    · exact ih (ops.drop 4) cell rest

theorem pack_flatten (n : Nat) (ops : List Opcode) : (pack n ops).flatten = ops.take (4 * n) := by
  induction n generalizing ops with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, List.flatten_cons, ih]
    rw [← List.take_add]
    congr 1
    omega

theorem cells_length (t : Tree) : (cells t).length = t.size := pack_length _ _

theorem cells_bound (t : Tree) : ∀ cell ∈ cells t, cell.length ≤ 4 := pack_cell_bound _ _

theorem cells_record (t : Tree) : (cells t).flatten = record t := by
  rw [cells, pack_flatten, List.take_of_length_le (record_length t)]

/-- Loading the packed snapshot retains no uncharged target-tree input. This
is the opcode/layout theorem; reading the cells on a buffer finger is separate. -/
theorem cells_restore (current saved : Tree) (same : current.size = saved.size) (cs : List Pointer.Frame) :
    replay (loadProgram current (cells saved).flatten) ⟨current, cs⟩ = some ⟨saved, cs⟩ := by
  rw [cells_record]
  exact load_replay current saved same cs

end RotationBST.TreeBuffer.Snapshot
