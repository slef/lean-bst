module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Chunks
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Correctness
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Completion
public import RotationBST.Structures.TreeBuffer.Cells.Effects
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording
open Multifinger

theorem Run.controller {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Controller.Run s.control ops t.control := by
  induction run with
  | done normal _ _ => exact normal
  | packet normal _ _ _ _ _ _ ih => exact normal.append ih

theorem Run.scan {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Scan.Trace s.scan t.scan w r := by
  induction run with
  | done _ _ _ => exact .refl
  | packet _ _ _ rotations _ writes _ ih =>
    simpa only [Nat.zero_add, Nat.add_zero] using rotations.append (writes.scan.append ih)

theorem Run.finished {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Controller.tick t.control = none ∧ t.scan.requests = [] := by
  induction run with
  | done _ halt empty => exact ⟨halt, empty⟩
  | packet _ _ _ _ _ _ _ ih => exact ih

theorem Run.rotations_le {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    r ≤ ops.length := by
  induction run with
  | done _ _ _ => exact Nat.le_refl _
  | packet _ _ _ _ bound _ _ ih => simp only [List.length_append]; omega

theorem Run.cost {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r)
    (valid : s.Valid) : w + ops.length ≤ 4 * s.scan.tree.size + 4 * ops.length := by
  have scan := run.scan.cost valid.2
  have rotations := run.rotations_le
  omega

theorem Run.valid {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r)
    (valid : s.Valid) : t.Valid := by
  induction run with
  | done normal _ _ =>
    have cursor := Option.some.inj normal.replay
    exact ⟨(congrArg Pointer.Config.tree cursor).symm.trans valid.1, valid.2⟩
  | packet _ _ _ rotations _ writes _ ih =>
    exact ih ⟨Cells.scan_fixed writes.scan rfl, writes.scan.valid (rotations.valid valid.2)⟩

theorem updated_requests (s : Scan.State) (tree : Tree) (size : s.tree.size = tree.size) :
    ({ s with tree := tree } : Scan.State).requests = s.requests := by
  simp only [Scan.State.requests, size]

/-- A finite local controller run whose output fits in the available cells
can be recorded online, one bounded packet and one cell write at a time. -/
theorem produce (s : State) (valid : s.Valid) (final : Controller.State) (ops : List Opcode)
    (normal : Controller.Run s.control ops final) (halt : Controller.tick final = none)
    (capacity : ops.length ≤ 4 * s.scan.requests.length) :
    ∃ t w r, Run s t ops w r ∧ t.control = final := by
  generalize amount : s.scan.requests.length = cells
  induction cells using Nat.strong_induction_on generalizing s ops with
  | ind cells ih =>
    by_cases empty : s.scan.requests = []
    · have noOps : ops = [] := List.eq_nil_of_length_eq_zero (by rw [empty, List.length_nil] at capacity; omega)
      subst ops
      exact ⟨⟨final, s.scan, s.data⟩, 0, 0, .done normal halt empty, rfl⟩
    · obtain ⟨control, emitted, rest, ready⟩ := normal.packet halt
      obtain ⟨rotations, rotationBound, shape⟩ := (replay_trace emitted.replay).rotations
      have scan := Streaming.rotations_scan shape s.scan valid.1.symm
      have unchanged := updated_requests s.scan control.cursor.tree scan.size_eq
      obtain ⟨next, work, writes, sequence⟩ := Cells.write_next _ (scan.valid valid.2)
        (by simpa only [unchanged] using empty) s.data (encodeCell (ops.take 4))
      rw [unchanged] at sequence
      have count : s.scan.requests.length = next.requests.length + 1 := by rw [sequence, List.length_cons]
      have smaller : next.requests.length < cells := by omega
      have nextValid : (State.mk control next (Function.update s.data s.scan.target (encodeCell (ops.take 4)))).Valid :=
        ⟨Cells.scan_fixed writes.scan rfl, writes.scan.valid (scan.valid valid.2)⟩
      have fits : (ops.drop 4).length ≤ 4 * next.requests.length := by
        simp only [List.length_drop]
        omega
      obtain ⟨t, later, more, tail, result⟩ := ih next.requests.length smaller _ nextValid (ops.drop 4)
        rest fits rfl
      refine ⟨t, work + later, rotations + more, ?_, result⟩
      simpa only [List.take_append_drop] using Run.packet emitted
        (by simp only [List.length_take]; exact Nat.min_le_left _ _) ready scan rotationBound writes tail

end RotationBST.TreeBuffer.Snapshot.Recording
