module

public import RotationBST.Structures.TreeBuffer.Cells.Operational
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Cells

theorem writeMany_apply {α : Type} (target : Nat → α) (keys : List Nat) (data : Nat → α) (x : Nat) :
    writeMany target keys data x = if x ∈ keys then target x else data x := by
  induction keys generalizing data with
  | nil => simp [writeMany]
  | cons y ys ih =>
    rw [writeMany, ih]
    by_cases later : x ∈ ys
    · simp [later]
    · by_cases first : x = y
      · subst x; simp [later]
      · simp [later, first]

/-- Lift any interleaved scan to reads of the actual node fields, with exactly
the same work and rotations. The returned list describes the read stream. -/
theorem lift_read {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (data : Nat → α) :
    ∃ keys, Trace ⟨s, data⟩ ⟨t, data⟩ (keys.map fun x => Event.read x (data x)) work rotations ∧
      s.requests = keys ++ t.requests := by
  induction trace generalizing data with
  | refl => exact ⟨[], .refl, rfl⟩
  | @step s t u k r h q first rest ih =>
    obtain ⟨keys, tail, sequence⟩ := ih (first.valid valid) data
    cases first with
    | move tree move key next pending closer =>
      refine ⟨keys, .step (.navigate tree move key next pending closer) tail, ?_⟩
      simpa only [Scan.State.requests, ← tree, move.tree_eq] using sequence
    | visit pending arrived =>
      refine ⟨s.position :: keys, .step (.read valid.1 pending arrived) tail, ?_⟩
      rw [Scan.requests_cons s pending, ← arrived, sequence]
      rfl
    | rotate rotation =>
      refine ⟨keys, .step (.rotate rotation) tail, ?_⟩
      simpa only [Scan.State.requests, ← rotation.size_eq] using sequence

/-- Lift the same scan to writes. `target` specifies the stream's desired values;
each machine action receives one value and writes only at the current cursor. -/
theorem lift_write {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (target data : Nat → α) :
    ∃ keys, Trace ⟨s, data⟩ ⟨t, writeMany target keys data⟩
      (keys.map fun x => Event.write x (target x)) work rotations ∧ s.requests = keys ++ t.requests := by
  induction trace generalizing data with
  | refl => exact ⟨[], .refl, rfl⟩
  | @step s t u k r h q first rest ih =>
    cases first with
    | move tree move key next pending closer =>
      obtain ⟨keys, tail, sequence⟩ := ih ((Scan.Step.move tree move key next pending closer).valid valid) data
      refine ⟨keys, .step (.navigate tree move key next pending closer) tail, ?_⟩
      simpa only [Scan.State.requests, ← tree, move.tree_eq] using sequence
    | visit pending arrived =>
      obtain ⟨keys, tail, sequence⟩ := ih ((Scan.Step.visit pending arrived).valid valid)
        (Function.update data s.position (target s.position))
      refine ⟨s.position :: keys, .step (.write (target s.position) valid.1 pending arrived) tail, ?_⟩
      rw [Scan.requests_cons s pending, ← arrived, sequence]
      rfl
    | rotate rotation =>
      obtain ⟨keys, tail, sequence⟩ := ih ((Scan.Step.rotate rotation).valid valid) data
      refine ⟨keys, .step (.rotate rotation) tail, ?_⟩
      simpa only [Scan.State.requests, ← rotation.size_eq] using sequence

/-- A completed scan reads every pending value in its specified order, even
when rotations interrupted the navigation. No payload changes are introduced. -/
theorem read_complete {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (done : t.requests = []) (data : Nat → α) :
    Trace ⟨s, data⟩ ⟨t, data⟩ (s.requests.map fun x => Event.read x (data x)) work rotations := by
  obtain ⟨keys, run, sequence⟩ := lift_read trace valid data
  rw [done, List.append_nil] at sequence
  simpa only [sequence] using run

/-- Completed writes set precisely the pending cells and leave every other
cell unchanged. Reordering or skipping a cell is excluded by the trace. -/
theorem write_complete {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (done : t.requests = []) (target data : Nat → α) :
    ∃ final, Trace ⟨s, data⟩ ⟨t, final⟩ (s.requests.map fun x => Event.write x (target x)) work rotations ∧
      ∀ x, final x = if x ∈ s.requests then target x else data x := by
  obtain ⟨keys, run, sequence⟩ := lift_write trace valid target data
  rw [done, List.append_nil] at sequence
  refine ⟨writeMany target keys data, by simpa only [sequence] using run, ?_⟩
  intro x
  rw [writeMany_apply, sequence]

end RotationBST.TreeBuffer.Cells
