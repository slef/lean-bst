module

public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording
open Multifinger

private theorem halted_empty {s t : Controller.State} {ops : List Opcode}
    (run : Controller.Run s ops t) (halt : Controller.tick s = none) : ops = [] := by
  cases run with
  | refl => rfl
  | silent first _ => rw [halt] at first; contradiction
  | instruction first _ => rw [halt] at first; contradiction

theorem pack_packet (chunk tail : List Opcode) (n : Nat) (fits : chunk.length ≤ 4)
    (boundary : chunk.length = 4 ∨ tail = []) :
    pack (n + 1) (chunk ++ tail) = chunk :: pack n tail := by
  rcases boundary with full | empty
  · simp only [pack, List.take_left' full, List.drop_left' full]
  · subst tail
    simp only [List.append_nil, pack, List.take_of_length_le fits, List.drop_eq_nil_of_le fits]

/-- The actual cell accesses write the canonical packed output, in exactly the
scan's initial key order. All intervening normalization rotations are included. -/
theorem Run.cells {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r)
    (valid : s.Valid) :
    Cells.Trace ⟨s.scan, s.data⟩ ⟨t.scan, t.data⟩
      (List.zipWith Cells.Event.write s.scan.requests ((pack s.scan.requests.length ops).map encodeCell)) w r := by
  induction run with
  | done normal halt empty => simpa only [empty, List.zipWith_nil_left] using (Cells.Trace.refl (s := ⟨_, _⟩))
  | @packet s u control chunk tail rotations work later more scan data key normal fits ready rotate bound writes rest ih =>
    have nextValid : (State.mk control scan data).Valid :=
      ⟨Cells.scan_fixed writes.scan rfl, writes.scan.valid (rotate.valid valid.2)⟩
    have tailCells := ih nextValid
    have unchanged := updated_requests s.scan control.cursor.tree rotate.size_eq
    have sequence := writes.requests
    simp only [List.map_cons, List.map_nil, Cells.Event.key, List.singleton_append] at sequence
    rw [unchanged] at sequence
    have boundary : chunk.length = 4 ∨ tail = [] := by
      rcases ready with full | halt
      · exact Or.inl full
      · exact Or.inr (halted_empty rest.controller halt)
    have packet := pack_packet chunk tail scan.requests.length fits boundary
    have cells := (Cells.rotations_only rotate valid.2 s.data).append (writes.append tailCells)
    simpa only [sequence, List.length_cons, packet, List.map_cons, List.zipWith_cons_cons,
      List.nil_append, List.singleton_append, Nat.zero_add, Nat.add_zero] using cells

end RotationBST.TreeBuffer.Snapshot.Recording
