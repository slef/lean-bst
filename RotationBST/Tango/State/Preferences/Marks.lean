module

public import RotationBST.Tango.State.Nesting.Edits.Whole

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

/-- Setting a preference is either a no-op, a first join, or a switch. All three
cases have a common bound in terms of the affected component's endpoint sizes. -/
theorem set_marks_in_component (outer : List Context.Frame) (boundary : Context.Boundary outer)
    (inner : List Context.Frame) (unmarked : ∀ f ∈ inner, f.marked = false)
    (s l r : MarkedTree) (cl cr next : Bool) (edge : cl = true ∨ cr = true) (H : Nat)
    (same : s.nesting = (Context.plug outer (Context.plug inner (.node l r cl cr))).nesting)
    (beforeBound : (Context.plug inner (.node l r cl cr)).region.size ≤ H)
    (afterBound : (Context.plug inner (.node l r (!next) next)).region.size ≤ H) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug outer (Context.plug inner (.node l r (!next) next))).nesting ∧
      Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
  have noOp (equal : cl = !next ∧ cr = next) :
      ∃ t : MarkedTree, ∃ cost : Nat,
        t.nesting = (Context.plug outer (Context.plug inner (.node l r (!next) next))).nesting ∧
        Rotations s.tree t.tree cost ∧
        (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
    refine ⟨s, 0, ?_, .refl, ?_⟩
    · simpa only [equal.1, equal.2] using same
    · have h := Bounds.logb_nat_nonneg H
      simp only [Nat.cast_zero, zero_add, sub_self]
      linarith
  cases cl <;> cases cr <;> cases next
  · simp at edge
  · simp at edge
  · exact switch_in_component outer boundary inner unmarked s l r true H same beforeBound afterBound
  · exact noOp ⟨rfl, rfl⟩
  · exact noOp ⟨rfl, rfl⟩
  · exact switch_in_component outer boundary inner unmarked s l r false H same beforeBound afterBound
  · obtain ⟨t, cost, hn, rotations, bound⟩ :=
      unmark_in_component outer boundary inner unmarked (.right l true true) r s same
    refine ⟨t, cost, hn, rotations, ?_⟩
    have mono := Splay.Updates.log_nat_mono afterBound
    have positive := Bounds.logb_nat_nonneg H
    simp only [Context.Frame.setMark, Context.Frame.fill, Bool.not_false] at bound mono
    linarith
  · obtain ⟨t, cost, hn, rotations, bound⟩ :=
      unmark_in_component outer boundary inner unmarked (.left r true true) l s same
    refine ⟨t, cost, hn, rotations, ?_⟩
    have mono := Splay.Updates.log_nat_mono afterBound
    have positive := Bounds.logb_nat_nonneg H
    simp only [Context.Frame.setMark, Context.Frame.fill, Bool.not_true] at bound mono
    linarith

end RotationBST.Tango
