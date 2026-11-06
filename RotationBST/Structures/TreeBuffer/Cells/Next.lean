module

public import RotationBST.Structures.TreeBuffer.Cells.Transfers
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

/-- Stop immediately after the next visit, without consuming later cells. -/
theorem scan_next (s : Scan.State) (valid : s.Valid) (pending : s.requests ≠ []) :
    ∃ t work, Scan.Trace s t work 0 ∧ s.requests = s.target :: t.requests := by
  generalize amount : Scan.potential s = fuel
  induction fuel using Nat.strong_induction_on generalizing s with
  | ind fuel ih =>
    obtain ⟨t, first⟩ := Scan.next_exists s valid pending
    have bound := first.potential_bound valid
    have smaller : Scan.potential t < fuel := by omega
    cases first with
    | @move a b y tree move key next pending closer =>
      have unchanged : ({ s with tree := b.tree, position := y } : Scan.State).requests = s.requests := by
        simp only [Scan.State.requests, ← tree, move.tree_eq]
      obtain ⟨u, work, tail, sequence⟩ := ih _ smaller _
        ((Scan.Step.move tree move key next pending closer).valid valid)
        (by simpa only [unchanged] using pending) rfl
      refine ⟨u, 1 + work, .step (.move tree move key next pending closer) tail, ?_⟩
      simpa only [unchanged, Scan.State.target] using sequence
    | visit pending arrived =>
      exact ⟨s.afterVisit, 1, .step (.visit pending arrived) .refl, Scan.requests_cons s pending⟩

/-- A supplied scalar is written to the next cell using charged navigation
and exactly one cursor-local write. This is the packet writer's blocking call. -/
theorem write_next {α : Type} (s : Scan.State) (valid : s.Valid) (pending : s.requests ≠ [])
    (data : Nat → α) (value : α) :
    ∃ t work, Trace ⟨s, data⟩ ⟨t, Function.update data s.target value⟩
      [.write s.target value] work 0 ∧ s.requests = s.target :: t.requests := by
  obtain ⟨t, work, scan, sequence⟩ := scan_next s valid pending
  obtain ⟨keys, run, prefixKeys⟩ := lift_write scan valid (fun _ => value) data
  have equality : [s.target] ++ t.requests = keys ++ t.requests := sequence.symm.trans prefixKeys
  have keys_eq : keys = [s.target] := (List.append_cancel_right equality).symm
  exact ⟨t, work, by simpa only [keys_eq, writeMany, List.map_cons, List.map_nil] using run, sequence⟩

end RotationBST.TreeBuffer.Cells
