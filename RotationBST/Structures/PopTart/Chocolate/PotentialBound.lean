module

public import RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract
public import RotationBST.Structures.PopTart.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

private theorem leafCount_positive (t : WeightedTree) : 0 < t.leafCount := by
  induction t with
  | leaf => exact Nat.zero_lt_one
  | node l r il ir => simp only [leafCount]; omega

private theorem attach_credit (rs : Regulars) (tail : WeightedTree) :
    rs.potential + 20 * tail.leafCount ≤ 20 * (rs.attach tail).leafCount := by
  cases rs with
  | zero => simp [Regulars.potential, Regulars.attach]
  | one a =>
      have := leafCount_positive a
      simp only [Regulars.potential, Regulars.attach, leafCount]
      omega
  | two a b =>
      simp only [Regulars.potential, Regulars.attach, leafCount]
      omega
  | three a b c =>
      have := leafCount_positive a
      simp only [Regulars.potential, Regulars.attach, leafCount]
      omega

mutual
/-- Repair credit counts outer separators, including those in frozen layers.
No payload nodes or validity assumptions are needed for this structural bound. -/
theorem layer_potential_bound (stack : Layer) :
    stack.potential + 20 ≤ 20 * stack.decode.leafCount := by
  cases stack with
  | last rs icing =>
      have ice := icing_potential_bound icing
      have outer := attach_credit rs icing.decode
      simp only [Layer.potential, Layer.decode]
      omega
  | next rs child icing =>
      have inner := layer_potential_bound child
      have ice := icing_potential_bound icing
      have outer := attach_credit rs (.node child.decode icing.decode)
      simp only [leafCount] at outer
      simp only [Layer.potential, Layer.decode]
      omega
termination_by sizeOf stack

theorem icing_potential_bound (icing : Icing) :
    icing.potential + 20 ≤ 20 * icing.decode.leafCount := by
  cases icing with
  | base crumb =>
      have := leafCount_positive crumb
      simp only [Icing.potential, Icing.decode]
      omega
  | solid crumb tail =>
      have rest := icing_potential_bound tail
      simp only [Icing.potential, Icing.decode, leafCount]
      omega
  | frozen carry old tail =>
      have before := layer_potential_bound old
      have rest := icing_potential_bound tail
      simp only [Icing.potential, Icing.decode, leafCount]
      omega
termination_by sizeOf icing
end

theorem layer_potential_fringe (stack : Layer) :
    stack.potential + 20 ≤ 20 * stack.decode.fringe.length := by
  simpa only [fringe_length] using layer_potential_bound stack

end RotationBST.PopTart.Chocolate
