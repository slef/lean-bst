module

public import RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Marking
public import RotationBST.Tango.State.Join.Interior

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Executable merging realizes exactly the requested nesting splice. -/
theorem mergeAt_spec (s child : MarkedTree) (i : Nat) (positive : 0 < s.region.size)
    (valid : i ≤ s.region.size) (attached : s.fringe[i]? = some child) :
    (s.mergeAt i).1.nesting = s.nesting.merge i ∧
      Rotations s.tree (s.mergeAt i).1.tree (s.mergeAt i).2 ∧
      ((s.mergeAt i).2 : ℝ) + (s.mergeAt i).1.potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + child.region.size : Nat) + 2 := by
  have log_nonneg := Bounds.logb_nat_nonneg (s.region.size + child.region.size)
  by_cases first : i = 0
  · subst i
    have head : s.fringe.head? = some child := by simpa only [List.head?_eq_getElem?] using attached
    obtain ⟨r, cr, result, hf, rotations, bound⟩ := joinFront_spec s child positive head
    have nested := unmark_left_nesting child r cr
    rw [← nesting_of_fringe hf] at nested
    simp only [mergeAt, ite_true]
    exact ⟨by simpa only [result] using nested, rotations, by linarith⟩
  · by_cases last : i = s.region.size
    · have tail : s.fringe.getLast? = some child := by
        simpa only [List.getLast?_eq_getElem?, marked_fringe_length, Nat.add_sub_cancel, last] using attached
      obtain ⟨l, cl, result, hf, rotations, bound⟩ := joinBack_spec s child positive tail
      have sizes := region_size_eq hf
      have rank : (if cl then 0 else l.region.size) + 1 = s.region.size := by
        cases cl <;> simp only [region, Pointer.Lazy.Skeleton.size, ite_true,
          Bool.false_eq_true, ite_false] at sizes ⊢ <;> omega
      have nested := unmark_right_nesting l child cl
      rw [← nesting_of_fringe hf, rank, ← last] at nested
      simp only [mergeAt, ite_eq_right first, ite_eq_left last]
      exact ⟨by simpa only [result] using nested, rotations, by linarith⟩
    · obtain ⟨a, c, ca, cc, result, rank, hf, rotations, bound⟩ :=
        joinInterior_spec s child i (by omega) (by omega) attached
      have nested := unmark_middle_nesting a child c ca cc
      rw [← nesting_of_fringe hf, rank] at nested
      simp only [mergeAt, ite_eq_right first, ite_eq_right last]
      exact ⟨by simpa only [result] using nested, rotations, bound⟩

end RotationBST.Tango.MarkedTree
