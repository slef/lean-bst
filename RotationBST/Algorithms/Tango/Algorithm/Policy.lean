module

public import RotationBST.Algorithms.Tango.Algorithm.Executable.Abstract

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

/-- Every policy satisfying the local contract serves its entire input with a
single telescoping potential bound. In particular, the policy is fixed before
the request sequence is chosen. -/
theorem Policy.runFrom_spec {reference : Tree} (p : Policy reference)
    (s : MarkedTree) (past xs : List Nat) (maintained : Maintains s reference past)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    Execution s.tree xs (p.runFrom past s xs).1.tree (p.runFrom past s xs).2 ∧
      Maintains (p.runFrom past s xs).1 reference (past ++ xs) ∧
      ((p.runFrom past s xs).2 : ℝ) + (p.runFrom past s xs).1.potential - s.potential ≤
        (preferenceLog reference past xs).length * (14 * Real.logb 2 (height reference) + 4) +
          xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  induction xs generalizing s past with
  | nil => exact ⟨.nil, by simpa [runFrom] using maintained, by simp [runFrom, preferenceLog]⟩
  | cons x xs ih =>
    have hx := valid x (List.mem_cons_self ..)
    obtain ⟨first, invariant, ba⟩ := p.correct past s x maintained history hx
    have extended : ∀ y ∈ past ++ [x], y < reference.size := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact history y hy
      · have h := List.mem_singleton.mp hy
        simpa only [h] using hx
    obtain ⟨remaining, finalInvariant, bb⟩ :=
      ih (p.step past s x).1 (past ++ [x]) invariant extended
        (fun y hy => valid y (List.mem_cons_of_mem _ hy))
    refine ⟨.cons first remaining, ?_, ?_⟩
    · simpa only [runFrom, List.append_assoc, List.singleton_append] using finalInvariant
    · simp only [runFrom, preferenceLog, List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem Policy.run_spec {reference : Tree} (p : Policy reference) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < reference.size) :
    Execution reference xs (p.run xs).1.tree (p.run xs).2 ∧ Maintains (p.run xs).1 reference xs ∧
      ((p.run xs).2 : ℝ) ≤
        (preferenceLog reference [] xs).length * (14 * Real.logb 2 (height reference) + 4) +
          xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  obtain ⟨execution, invariant, bound⟩ := p.runFrom_spec (initial reference) [] xs
    (initial_maintains reference) (by simp) valid
  refine ⟨?_, ?_, ?_⟩
  · simpa only [run, initial_tree] using execution
  · simpa only [run, List.nil_append] using invariant
  · have nonnegative := potential_nonneg (p.run xs).1
    rw [initial_potential] at bound
    change ((p.run xs).2 : ℝ) + (p.run xs).1.potential - 0 ≤ _ at bound
    linarith

end RotationBST.Tango
