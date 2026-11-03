module

public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Join

private theorem finish_growth (h : Nat) (result : Promotion × Nat)
    (growth : h < (finish h result).height) : rootKeys (finish h result).tree = 1 := by
  obtain ⟨up, cost⟩ := result
  cases up with
  | stay t => simp [finish] at growth
  | rise l r => rfl

/-- Any genuine height increase creates a minimal root, leaving room for a
later separator to be absorbed instead of causing another increase. -/
theorem run_growth (hl hr : Nat) (l r : Multiway)
    (growth : max hl hr < (run hl hr l r).height) : rootKeys (run hl hr l r).tree = 1 := by
  by_cases le : hr ≤ hl <;> simp only [run, le, ite_true, ite_false] at growth ⊢
  · apply finish_growth
    omega
  · apply finish_growth
    omega

theorem compact_growth (hl hr : Nat) (l r : Multiway)
    (growth : max hl hr < (compact hl hr l r).height) : rootKeys (compact hl hr l r).tree = 1 := by
  by_cases eq : hl = hr
  · subst hr
    cases l <;> cases r <;> simp only [compact, ite_true] at growth ⊢ <;>
      first | exact run_growth _ _ _ _ growth | simp at growth
  · simp only [compact, eq, ite_false] at growth ⊢
    exact run_growth _ _ _ _ growth

/-- A taller minimal root absorbs the join and has at most two separators. -/
theorem compact_taller_two_left {hl hr : Nat} (taller : hr < hl) (a b r : Multiway) :
    (compact hl hr (.two a b) r).height = hl ∧
      rootKeys (compact hl hr (.two a b) r).tree ≤ 2 := by
  have ne : hl ≠ hr := by omega
  have le : hr ≤ hl := by omega
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hl - hr ≠ 0 by omega)
  simp only [compact, ne, ite_false, run, le, ite_true, diff, joinRight]
  cases result : joinRight d b r with
  | mk up cost => cases up <;> simp [finish, rootKeys]

theorem compact_taller_two_right {hl hr : Nat} (taller : hl < hr) (l a b : Multiway) :
    (compact hl hr l (.two a b)).height = hr ∧
      rootKeys (compact hl hr l (.two a b)).tree ≤ 2 := by
  have ne : hl ≠ hr := by omega
  have le : ¬hr ≤ hl := by omega
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hr - hl ≠ 0 by omega)
  simp only [compact, ne, ite_false, run, le, diff, joinLeft]
  cases result : joinLeft d l a with
  | mk up cost => cases up <;> simp [finish, rootKeys]

end RotationBST.Arboral.Split.Multiway.Join
