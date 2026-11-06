module

public import RotationBST.Structures.TreeBuffer.Snapshot.Storage
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot
open Multifinger

theorem opcodeDigit_bounds (op : Opcode) : 0 < opcodeDigit op ∧ opcodeDigit op < 7 := by
  cases op <;> decide

theorem digitOpcode_inverse (op : Opcode) : digitOpcode (opcodeDigit op) = some op := by cases op <;> rfl

theorem encodeCell_bound (ops : List Opcode) : encodeCell ops < 7 ^ ops.length := by
  induction ops with
  | nil => simp [encodeCell]
  | cons op ops ih =>
    have bounds := opcodeDigit_bounds op
    simp only [encodeCell, List.length_cons, pow_succ]
    omega

/-- Every packet emitted by the recording controller fits the snapshot field. -/
theorem encodeCell_packet_bound (ops : List Opcode) (capacity : ops.length ≤ 4) :
    encodeCell ops < 2 ^ 12 := by
  have bound := encodeCell_bound ops
  have powers : 7 ^ ops.length ≤ 7 ^ 4 := Nat.pow_le_pow_right (by decide) capacity
  omega

theorem decodeFuel_encode (fuel : Nat) (ops : List Opcode) (fits : ops.length ≤ fuel) :
    decodeFuel fuel (encodeCell ops) = ops := by
  induction fuel generalizing ops with
  | zero => have empty := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero fits); subst ops; rfl
  | succ fuel ih =>
    cases ops with
    | nil => rfl
    | cons op ops =>
      have rest : ops.length ≤ fuel := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using fits
      have bounds := opcodeDigit_bounds op
      have remainder : (opcodeDigit op + 7 * encodeCell ops) % 7 = opcodeDigit op := by omega
      have quotient : (opcodeDigit op + 7 * encodeCell ops) / 7 = encodeCell ops := by omega
      simp only [encodeCell, decodeFuel, remainder, quotient, digitOpcode_inverse, ih ops rest]

theorem decodeCell_encode (ops : List Opcode) (fits : ops.length ≤ 4) : decodeCell (encodeCell ops) = ops :=
  decodeFuel_encode 4 ops fits

theorem encodedCells_length (t : Tree) : (encodedCells t).length = t.size := by
  simp only [encodedCells, List.length_map, cells_length]

/-- Every cell fits in twelve bits, independently of tree size. This counts
payload bits; it does not assert a buffer-access or allocator implementation. -/
theorem encodedCells_bound (t : Tree) : ∀ code ∈ encodedCells t, code < 2 ^ 12 := by
  intro code member
  obtain ⟨cell, stored, rfl⟩ := List.mem_map.mp member
  exact encodeCell_packet_bound cell (cells_bound t cell stored)

theorem decodeCells_encoded (t : Tree) : decodeCells (encodedCells t) = record t := by
  have identity : (cells t).map (fun cell => decodeCell (encodeCell cell)) = (cells t).map id := by
    apply List.map_congr_left
    intro cell member
    exact decodeCell_encode cell (cells_bound t cell member)
  simp only [decodeCells, encodedCells, List.map_map, Function.comp_def]
  rw [identity, List.map_id, cells_record]

theorem loadEncoded_replay (current saved : Tree) (same : current.size = saved.size) (cs : List Pointer.Frame) :
    replay (loadEncoded current (encodedCells saved)) ⟨current, cs⟩ = some ⟨saved, cs⟩ := by
  rw [loadEncoded, decodeCells_encoded]
  exact load_replay current saved same cs

theorem loadEncoded_length (current saved : Tree) (same : current.size = saved.size) :
    (loadEncoded current (encodedCells saved)).length ≤ 16 * current.size := by
  rw [loadEncoded, decodeCells_encoded]
  exact load_length current saved same

end RotationBST.TreeBuffer.Snapshot
