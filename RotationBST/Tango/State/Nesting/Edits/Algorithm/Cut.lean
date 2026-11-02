module

public import RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Marking
public import RotationBST.Tango.State.Cut.Interior

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem nonempty_of_region {s : MarkedTree} (positive : 0 < s.region.size) : s ≠ .nil := by
  intro h
  subst s
  exact Nat.not_lt_zero _ positive

/-- Executable interval cutting realizes exactly the required nesting group. -/
theorem cutInterval_spec (s : MarkedTree) (i j : Nat) (ordered : i < j)
    (valid : j ≤ s.region.size) (proper : j - i < s.region.size) :
    (s.cutInterval i j).1.nesting = s.nesting.group i (j - i + 1) ∧
      Rotations s.tree (s.cutInterval i j).1.tree (s.cutInterval i j).2 ∧
      ((s.cutInterval i j).2 : ℝ) + (s.cutInterval i j).1.potential - s.potential ≤
        6 * Real.logb 2 s.region.size + 2 := by
  have log_nonneg := Bounds.logb_nat_nonneg s.region.size
  by_cases first : i = 0
  · subst i
    obtain ⟨l, r, cr, result, rank, hf, rotations, bound⟩ := cutPrefix_spec s j (by omega) (by omega)
    have nested := mark_left_nesting l r cr (nonempty_of_region (by omega))
    rw [← nesting_of_fringe hf, rank] at nested
    simp only [cutInterval, ite_true]
    refine ⟨?_, rotations, by linarith⟩
    simpa only [result, Nat.sub_zero] using nested
  · by_cases last : j = s.region.size
    · obtain ⟨l, r, cl, result, rank, count, hf, rotations, bound⟩ := cutSuffix_spec s i (by omega) (by omega)
      have nested := mark_right_nesting l r cl (nonempty_of_region (by omega))
      rw [← nesting_of_fringe hf, rank, count, ← last] at nested
      simp only [cutInterval, ite_eq_right first, ite_eq_left last]
      exact ⟨by simpa only [result] using nested, rotations, by linarith⟩
    · obtain ⟨a, middle, c, ca, cc, result, rank, count, hf, rotations, bound⟩ :=
        cutInterior_spec s i j (by omega) ordered (by omega)
      have nested := mark_middle_nesting a middle c ca cc (nonempty_of_region (by omega))
      rw [← nesting_of_fringe hf, rank, count] at nested
      simp only [cutInterval, ite_eq_right first, ite_eq_right last]
      exact ⟨by simpa only [result] using nested, rotations, bound⟩

end RotationBST.Tango.MarkedTree
