module

public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Wilber
open Context

/-- A compiled preference switch retains the same logarithmic bound as the
existential simulation, independently of the number of unmarked ancestors. -/
theorem switchInPath_spec (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (plug fs (.node l r (!left) left)).nesting)
    (beforeBound : (plug fs (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (plug fs (.node l r left (!left))).region.size ≤ H) :
    (s.switchInPath fs l r left).1.nesting = (plug fs (.node l r left (!left))).nesting ∧
      Rotations s.tree (s.switchInPath fs l r left).1.tree (s.switchInPath fs l r left).2 ∧
      ((s.switchInPath fs l r left).2 : ℝ) + (s.switchInPath fs l r left).1.potential - s.potential ≤
        14 * Real.logb 2 H + 4 := by
  cases left
  · obtain ⟨ha, ra, ba⟩ := markInPath_spec s fs unmarked (.right l false true) r same
    obtain ⟨hb, rb, bb⟩ := unmarkInPath_spec (s.markInPath fs (.right l false true) r).1 fs unmarked
      (.left r false true) l ha
    refine ⟨hb, ra.append rb, ?_⟩
    have beforeLog := Splay.Updates.log_nat_mono beforeBound
    have afterLog := Splay.Updates.log_nat_mono afterBound
    simp only [Bool.not_false] at beforeLog afterLog
    simp only [plug, Frame.setMark, Frame.fill] at ba bb
    simp only [switchInPath, Bool.false_eq_true, ite_false, Nat.cast_add]
    linarith
  · obtain ⟨ha, ra, ba⟩ := markInPath_spec s fs unmarked (.left r false true) l same
    obtain ⟨hb, rb, bb⟩ := unmarkInPath_spec (s.markInPath fs (.left r false true) l).1 fs unmarked
      (.right l false true) r ha
    refine ⟨hb, ra.append rb, ?_⟩
    have beforeLog := Splay.Updates.log_nat_mono beforeBound
    have afterLog := Splay.Updates.log_nat_mono afterBound
    simp only [Bool.not_true] at beforeLog afterLog
    simp only [plug, Frame.setMark, Frame.fill] at ba bb
    simp only [switchInPath, ite_true, Nat.cast_add]
    linarith

end RotationBST.Tango.MarkedTree
