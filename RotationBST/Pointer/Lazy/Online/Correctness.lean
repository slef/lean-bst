module

public import RotationBST.Pointer.Lazy.Online.Algorithm.Abstract

@[expose] public section

namespace RotationBST.Pointer.Lazy.Online

theorem advance_spec (a : Algorithm) (past : List Nat) (s : State) (x : Nat)
    (valid : x < s.virtual.size) : Transition a past s x (advance a past s x) := by
  rw [advance, dite_eq_left valid]
  exact Classical.choose_spec (advance_exists a past s x valid)

/-- Prefix composition makes the absence of lookahead explicit. -/
theorem run_append (a : Algorithm) (past : List Nat) (s : State) (xs ys : List Nat) :
    run a past s (xs ++ ys) =
      let first := run a past s xs
      let rest := run a (past ++ xs) first.1 ys
      (rest.1, first.2 + rest.2) := by
  induction xs generalizing past s with
  | nil => simp [run]
  | cons x xs ih => simp only [List.cons_append, run, ih, List.append_assoc, List.nil_append, Nat.add_assoc]

/-- Causal simulation, preserving the virtual execution and amortizing all
postponed rotations. -/
theorem run_spec (a : Algorithm) (past : List Nat) (s : State) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < s.virtual.size) :
    (run a past s xs).1.virtual = (a.runFrom past s.virtual xs).1 ∧
    Pointer.Execution s.current xs (run a past s xs).1.current (run a past s xs).2 ∧
    (run a past s xs).2 + 32 * (run a past s xs).1.pending ≤
      32 * (s.pending + (a.runFrom past s.virtual xs).2) + 17 * xs.length := by
  induction xs generalizing past s with
  | nil => exact ⟨rfl, .nil, by simp [run, Algorithm.runFrom]⟩
  | cons x xs ih =>
      have hx := valid x (by simp)
      obtain ⟨hserve, hvirtual, hcost⟩ := advance_spec a past s x hx
      have hsize : (advance a past s x).1.virtual.size = s.virtual.size := by
        rw [hvirtual]
        exact (a.correct past s.virtual x hx).1.size_eq.symm
      have hv : ∀ y ∈ xs, y < (advance a past s x).1.virtual.size := by
        intro y hy
        rw [hsize]
        exact valid y (by simp [hy])
      obtain ⟨heq, hexec, hbound⟩ := ih (past ++ [x]) (advance a past s x).1 hv
      refine ⟨?_, ?_, ?_⟩
      · simpa only [run, Algorithm.runFrom, hvirtual] using heq
      · exact .cons hserve hexec
      · simp only [run, Algorithm.runFrom, List.length_cons]
        rw [hvirtual] at hbound
        change (advance a past s x).2 + (run a (past ++ [x]) (advance a past s x).1 xs).2 +
          32 * (run a (past ++ [x]) (advance a past s x).1 xs).1.pending ≤
          32 * (s.pending + ((a.step past s.virtual x).2 +
            (a.runFrom (past ++ [x]) (a.step past s.virtual x).1 xs).2)) + 17 * (xs.length + 1)
        omega

end RotationBST.Pointer.Lazy.Online
