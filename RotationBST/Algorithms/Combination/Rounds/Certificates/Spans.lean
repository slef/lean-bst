module

public import RotationBST.Algorithms.Combination.Rounds.Certificates.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Rounds.Accounting

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates

private theorem partition_nonempty (side : Bool) (start stop : Nat) (boundaries : List Nat) :
    partition side start stop boundaries ≠ [] := by cases boundaries <;> simp [partition]

/-- The operational records have exactly the coverage spans previously used
in the charge analysis, excluding the final round, which has not switched away. -/
theorem records_spans {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) :
    (records worker budget restore s start offset earlier xs).map Record.span =
      (partition s.side start (offset + xs.length) (cuts worker budget restore s offset xs)).dropLast := by
  induction xs generalizing s start offset earlier with
  | nil => simp [records, cuts, partition]
  | cons x xs ih =>
    have side := Controller.serve_alternates worker budget restore s x
    by_cases done : (Controller.serve worker budget restore s x).done = true
    · by_cases changed : (Controller.serve worker budget restore s x).switched = true
      · simp only [changed, ↓reduceIte] at side
        simp only [records, cuts, done, changed, ↓reduceIte, List.map_cons, ih, partition,
          List.dropLast_cons_of_ne_nil (partition_nonempty _ _ _ _), side, List.length_cons, Nat.add_comm, Nat.add_left_comm]
      · simp only [changed, Bool.false_eq_true, ↓reduceIte] at side
        simpa only [records, cuts, done, changed, Bool.false_eq_true, ↓reduceIte, side, List.length_cons,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (Controller.serve worker budget restore s x).state start (offset + 1) (earlier ++ [x])
    · simp [records, cuts, done, partition]

/-- All recorded span endpoints stay in the covered prefix. The current
round may already have completed requests before `offset`. -/
theorem records_bounds {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) (before : start ≤ offset) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      start ≤ record.span.start ∧ record.span.start ≤ record.span.stop ∧ record.span.stop ≤ offset + xs.length := by
  intro record member
  have mapped : record.span ∈ (records worker budget restore s start offset earlier xs).map Record.span :=
    List.mem_map.mpr ⟨record, member, rfl⟩
  rw [records_spans] at mapped
  have inPartition := List.mem_of_mem_dropLast mapped
  obtain ⟨ordered, inside⟩ := cuts_ordered worker budget restore s offset xs
  exact partition_bounds s.side start (offset + xs.length) _ (by omega) ordered
    (fun i member => ⟨by have := (inside i member).1; omega, (inside i member).2⟩) record.span inPartition

end RotationBST.Combo.Rounds.Certificates
