module

public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Defs
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Switch

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Context

/-- The compiled local update obeys a uniform bound for all possible old marks. -/
theorem setMarksInPath_spec (s : MarkedTree) (fs : List Frame)
    (unmarked : ∀ f ∈ fs, f.marked = false) (l r : MarkedTree)
    (cl cr next : Bool) (edge : cl = true ∨ cr = true) (H : Nat)
    (same : s.nesting = (plug fs (.node l r cl cr)).nesting)
    (beforeBound : (plug fs (.node l r cl cr)).region.size ≤ H)
    (afterBound : (plug fs (.node l r (!next) next)).region.size ≤ H) :
    (s.setMarksInPath fs l r cl cr next).1.nesting = (plug fs (.node l r (!next) next)).nesting ∧
      Rotations s.tree (s.setMarksInPath fs l r cl cr next).1.tree
        (s.setMarksInPath fs l r cl cr next).2 ∧
      ((s.setMarksInPath fs l r cl cr next).2 : ℝ) +
        (s.setMarksInPath fs l r cl cr next).1.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
  have noOp : (0 : ℝ) + s.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
    have positive := Bounds.logb_nat_nonneg H
    linarith
  cases cl <;> cases cr <;> cases next
  · simp at edge
  · simp at edge
  · exact switchInPath_spec s fs unmarked l r true H same beforeBound afterBound
  · exact ⟨same, .refl, by simpa [setMarksInPath] using noOp⟩
  · exact ⟨same, .refl, by simpa [setMarksInPath] using noOp⟩
  · exact switchInPath_spec s fs unmarked l r false H same beforeBound afterBound
  · obtain ⟨nested, rotations, bound⟩ := unmarkKnownInPath_bound s fs unmarked (.right l true true) r same
    refine ⟨nested, rotations, ?_⟩
    have mono := Splay.Updates.log_nat_mono afterBound
    have positive := Bounds.logb_nat_nonneg H
    simp only [Context.Frame.setMark, Context.Frame.fill, Bool.not_false, plug] at bound mono
    change ((s.unmarkKnownInPath fs (.right l true true) r).2 : ℝ) +
      (s.unmarkKnownInPath fs (.right l true true) r).1.potential - s.potential ≤ _
    linarith
  · obtain ⟨nested, rotations, bound⟩ := unmarkKnownInPath_bound s fs unmarked (.left r true true) l same
    refine ⟨nested, rotations, ?_⟩
    have mono := Splay.Updates.log_nat_mono afterBound
    have positive := Bounds.logb_nat_nonneg H
    simp only [Context.Frame.setMark, Context.Frame.fill, Bool.not_true, plug] at bound mono
    change ((s.unmarkKnownInPath fs (.left r true true) l).2 : ℝ) +
      (s.unmarkKnownInPath fs (.left r true true) l).1.potential - s.potential ≤ _
    linarith

end RotationBST.Tango.MarkedTree
