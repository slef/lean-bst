module

public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Edges
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Switch

@[expose] public section
namespace RotationBST.Tango
open Wilber
open MarkedTree

/-- Mark an edge anywhere within a reference component. The operation is
realized at its actual auxiliary root, so the number of ancestors adds no cost. -/
theorem mark_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug fs ((f.setMark false).fill child)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs ((f.setMark true).fill child)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        6 * Real.logb 2 (Context.plug fs ((f.setMark false).fill child)).region.size + 2 := by
  exact ⟨(s.markInPath fs f child).1, (s.markInPath fs f child).2,
    markInPath_spec s fs unmarked f child same⟩

/-- Remove a mark anywhere within the parent reference component. -/
theorem unmark_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug fs ((f.setMark true).fill child)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs ((f.setMark false).fill child)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (Context.plug fs ((f.setMark false).fill child)).region.size + 2 := by
  exact ⟨(s.unmarkInPath fs f).1, (s.unmarkInPath fs f).2,
    unmarkInPath_spec s fs unmarked f child same⟩

/-- Switch from left to right at any node of a preferred path. Both endpoint
component sizes are explicit, for the later reference-height bound. -/
theorem switch_right_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (s l r : MarkedTree) (same : s.nesting = (Context.plug fs (.node l r false true)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs (.node l r true false)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        6 * Real.logb 2 (Context.plug fs (.node l r false true)).region.size +
        8 * Real.logb 2 (Context.plug fs (.node l r true false)).region.size + 4 := by
  obtain ⟨u, a, hu, ra, ba⟩ := mark_in_path fs unmarked (.left r false true) l s same
  obtain ⟨t, b, ht, rb, bb⟩ := unmark_in_path fs unmarked (.right l false true) r u hu
  refine ⟨t, a + b, ht, ra.append rb, ?_⟩
  simp only [Context.Frame.setMark, Context.Frame.fill] at ba bb
  simp only [Nat.cast_add]
  linarith

theorem switch_left_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (s l r : MarkedTree) (same : s.nesting = (Context.plug fs (.node l r true false)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs (.node l r false true)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        6 * Real.logb 2 (Context.plug fs (.node l r true false)).region.size +
        8 * Real.logb 2 (Context.plug fs (.node l r false true)).region.size + 4 := by
  obtain ⟨u, a, hu, ra, ba⟩ := mark_in_path fs unmarked (.right l false true) r s same
  obtain ⟨t, b, ht, rb, bb⟩ := unmark_in_path fs unmarked (.left r false true) l u hu
  refine ⟨t, a + b, ht, ra.append rb, ?_⟩
  simp only [Context.Frame.setMark, Context.Frame.fill] at ba bb
  simp only [Nat.cast_add]
  linarith

/-- A preference switch anywhere in a bounded component costs logarithmically
in the component-size bound, independently of its reference depth. -/
theorem switch_in_path_bound (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (s l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (Context.plug fs (.node l r (!left) left)).nesting)
    (beforeBound : (Context.plug fs (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (Context.plug fs (.node l r left (!left))).region.size ≤ H) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs (.node l r left (!left))).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
  exact ⟨(s.switchInPath fs l r left).1, (s.switchInPath fs l r left).2,
    switchInPath_spec s fs unmarked l r left H same beforeBound afterBound⟩

end RotationBST.Tango
