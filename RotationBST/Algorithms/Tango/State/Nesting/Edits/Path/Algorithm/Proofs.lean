module

public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Defs
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Offsets
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Simulation

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Context

theorem markInPath_spec (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark false) :: fs) child).nesting) :
    (s.markInPath fs f child).1.nesting = (plug ((f.setMark true) :: fs) child).nesting ∧
      Rotations s.tree (s.markInPath fs f child).1.tree (s.markInPath fs f child).2 ∧
      ((s.markInPath fs f child).2 : ℝ) + (s.markInPath fs f child).1.potential - s.potential ≤
        6 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 := by
  by_cases empty : child = .nil
  · subst child
    obtain ⟨source, target⟩ := edge_nesting fs unmarked f .nil
    have equal : (plug ((f.setMark false) :: fs) .nil).nesting =
        (plug ((f.setMark true) :: fs) .nil).nesting := by rw [source, target]; rfl
    simp only [markInPath, ite_true]
    refine ⟨same.trans equal, .refl, ?_⟩
    have h := Bounds.logb_nat_nonneg (plug ((f.setMark false) :: fs) .nil).region.size
    simp only [Nat.cast_zero, zero_add, sub_self]
    linarith
  · have positive : 0 < child.region.size := by cases child <;> simp_all [region, Pointer.Lazy.Skeleton.size]
    have sizes := (edge_sizes fs unmarked f child).1
    have remaining := edge_remaining f fs
    have bound := cutInterval_simulates s (plug ((f.setMark false) :: fs) child) same
      (before (f :: fs)).length ((before (f :: fs)).length + child.region.size)
      (by omega) (by omega) (by omega)
    simp only [markInPath, ite_eq_right empty]
    rw [Nat.add_sub_cancel_left, ← mark_path_group fs unmarked f child empty] at bound
    exact bound

theorem unmarkInPath_spec (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark true) :: fs) child).nesting) :
    (s.unmarkInPath fs f).1.nesting = (plug ((f.setMark false) :: fs) child).nesting ∧
      Rotations s.tree (s.unmarkInPath fs f).1.tree (s.unmarkInPath fs f).2 ∧
      ((s.unmarkInPath fs f).2 : ℝ) + (s.unmarkInPath fs f).1.potential - s.potential ≤
        8 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 := by
  obtain ⟨sourceSize, targetSize⟩ := edge_sizes fs unmarked f child
  have remaining := edge_remaining f fs
  have bound := mergeAt_simulates s (plug ((f.setMark true) :: fs) child) child same
    (before (f :: fs)).length (by omega) (by omega) (edge_slot fs unmarked f child)
  have total : (plug ((f.setMark true) :: fs) child).region.size + child.region.size =
      (plug ((f.setMark false) :: fs) child).region.size := by omega
  rw [total, ← unmark_path_merge fs unmarked f child] at bound
  exact bound

/-- Avoid a boundary splay for an empty reference child while preserving
the same nesting and amortized guarantee as the general join compiler. -/
theorem unmarkKnownInPath_spec (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ g ∈ fs, g.marked = false) (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark true) :: fs) child).nesting) :
    (s.unmarkKnownInPath fs f child).1.nesting = (plug ((f.setMark false) :: fs) child).nesting ∧
      Rotations s.tree (s.unmarkKnownInPath fs f child).1.tree (s.unmarkKnownInPath fs f child).2 ∧
      ((s.unmarkKnownInPath fs f child).2 : ℝ) + (s.unmarkKnownInPath fs f child).1.potential - s.potential ≤
        if child = .nil then 0 else 8 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 := by
  by_cases empty : child = .nil
  · subst child
    obtain ⟨source, target⟩ := edge_nesting fs unmarked f .nil
    have equal : (plug ((f.setMark true) :: fs) .nil).nesting =
        (plug ((f.setMark false) :: fs) .nil).nesting := by rw [source, target]; rfl
    simp only [unmarkKnownInPath, ite_true]
    exact ⟨same.trans equal, .refl, by simp⟩
  · simpa only [unmarkKnownInPath, ite_eq_right empty] using unmarkInPath_spec s fs unmarked f child same

theorem unmarkKnownInPath_bound (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ g ∈ fs, g.marked = false) (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark true) :: fs) child).nesting) :
    (s.unmarkKnownInPath fs f child).1.nesting = (plug ((f.setMark false) :: fs) child).nesting ∧
      Rotations s.tree (s.unmarkKnownInPath fs f child).1.tree (s.unmarkKnownInPath fs f child).2 ∧
      ((s.unmarkKnownInPath fs f child).2 : ℝ) + (s.unmarkKnownInPath fs f child).1.potential - s.potential ≤
        8 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 := by
  obtain ⟨nested, rotations, bound⟩ := unmarkKnownInPath_spec s fs unmarked f child same
  refine ⟨nested, rotations, ?_⟩
  split at bound
  · have positive := Bounds.logb_nat_nonneg (plug ((f.setMark false) :: fs) child).region.size
    linarith
  · exact bound

end RotationBST.Tango.MarkedTree
