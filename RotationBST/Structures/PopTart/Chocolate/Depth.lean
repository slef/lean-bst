module

public import RotationBST.Structures.PopTart.Chocolate.Regulars
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

private theorem ratio_log_nonnegative {t : WeightedTree} (nonnegative : t.Nonnegative)
    {subtree : Tree} {weight : ℝ} {depth : Nat} (slot : SlotAt t subtree weight depth)
    (positive : 0 < weight) : 0 ≤ Real.logb 2 (t.mass / weight) := by
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact (le_div_iff₀ positive).mpr (by simpa only [one_mul] using (slot_le_mass slot nonnegative).2)

private theorem ratio_log_mono {small big weight : ℝ} (smallPositive : 0 < small)
    (positive : 0 < weight) (bound : small ≤ big) :
    Real.logb 2 (small / weight) ≤ Real.logb 2 (big / weight) :=
  Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos smallPositive positive)
    (div_le_div_of_nonneg_right bound positive.le)

private theorem ratio_log_double {small big weight : ℝ} (smallPositive : 0 < small)
    (positive : 0 < weight) (bound : 2 * small ≤ big) :
    Real.logb 2 (small / weight) + 1 ≤ Real.logb 2 (big / weight) := by
  have ratio : 2 * (small / weight) ≤ big / weight := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right bound positive.le
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos (by norm_num) (div_pos smallPositive positive)) ratio
  rw [Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (div_pos smallPositive positive))] at logarithm
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), add_comm] using logarithm

mutual
/-- Weighted depth includes every original fringe occurrence, including those
inside recursively frozen layers. The additive seven accounts for the full
regular/next/icing path at the current layer. -/
theorem layer_depth {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ (level : ℝ) + 7 + 7 * Real.logb 2 (stack.decode.mass / weight) := by
  have logNonnegative := ratio_log_nonnegative (layer_nonnegative valid) slot positive
  cases stack with
  | last rs icing =>
    rcases attach_slot valid.1 slot with regular | ⟨d, found, distance⟩
    · have bound : (depth : ℝ) ≤ (level : ℝ) + 3 := by exact_mod_cast regular
      linarith only [bound, logNonnegative]
    · have bound := icing_leaf_depth valid.2.1 found positive
      have positiveMass := positive.trans_le (slot_le_mass found (icing_nonnegative valid.2.1)).2
      have logarithm := ratio_log_mono positiveMass positive (attach_mass valid.1 icing.decode)
      have realDistance : (depth : ℝ) ≤ (d : ℝ) + 3 := by exact_mod_cast distance
      change (depth : ℝ) ≤ (level : ℝ) + 7 + 7 * Real.logb 2 ((rs.attach icing.decode).mass / weight)
      linarith only [bound, logarithm, realDistance]
  | next rs child icing =>
    rcases attach_slot valid.1 slot with regular | ⟨d, found, distance⟩
    · have bound : (depth : ℝ) ≤ (level : ℝ) + 3 := by exact_mod_cast regular
      linarith only [bound, logNonnegative]
    · have suffixMass := attach_mass valid.1 (.node child.decode icing.decode)
      change child.decode.mass + icing.decode.mass ≤ (Layer.next rs child icing).decode.mass at suffixMass
      have realDistance : (depth : ℝ) ≤ (d : ℝ) + 3 := by exact_mod_cast distance
      cases found with
      | left childSlot =>
        have bound := layer_depth valid.2.1 childSlot positive
        have positiveMass := positive.trans_le (slot_le_mass childSlot (layer_nonnegative valid.2.1)).2
        have half : 2 * child.decode.mass ≤ (Layer.next rs child icing).decode.mass := by
          have thick := valid.2.2.2.2
          linarith only [thick, suffixMass]
        have logarithm := ratio_log_double positiveMass positive half
        simp only [Nat.cast_add, Nat.cast_one] at bound realDistance
        linarith only [bound, logarithm, realDistance]
      | right iceSlot =>
        have bound := icing_leaf_depth valid.2.2.1 iceSlot positive
        have positiveMass := positive.trans_le (slot_le_mass iceSlot (icing_nonnegative valid.2.2.1)).2
        have massBound : icing.decode.mass ≤ (Layer.next rs child icing).decode.mass := by
          have childMass := mass_nonnegative (layer_nonnegative valid.2.1)
          linarith only [suffixMass, childMass]
        have logarithm := ratio_log_mono positiveMass positive massBound
        simp only [Nat.cast_add, Nat.cast_one] at realDistance
        linarith only [bound, logarithm, realDistance]
termination_by sizeOf stack

/-- Depth inside icing includes the interiors of its frozen blocks. The
saved old-next-layer inequality pays for descending into a frozen layer. -/
theorem icing_leaf_depth {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ (level : ℝ) + 3 + 7 * Real.logb 2 (icing.decode.mass / weight) := by
  have logNonnegative := ratio_log_nonnegative (icing_nonnegative valid) slot positive
  cases icing with
  | base crumb =>
    rw [perfect_depth valid.1 slot]
    linarith only [logNonnegative]
  | solid crumb tail =>
    cases slot with
    | left found =>
      rw [perfect_depth valid.1 found]
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [logNonnegative]
    | right found =>
      have bound := icing_leaf_depth valid.2.2.1 found positive
      have positiveMass := positive.trans_le (slot_le_mass found (icing_nonnegative valid.2.2.1)).2
      have half : 2 * tail.decode.mass ≤ (Icing.solid crumb tail).decode.mass := by
        have dominates := valid.2.2.2
        change 2 * tail.decode.mass ≤ crumb.mass + tail.decode.mass
        linarith only [dominates]
      have logarithm := ratio_log_double positiveMass positive half
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [bound, logarithm]
  | frozen carry old tail =>
    cases slot with
    | left found =>
      cases found with
      | left hit =>
        rw [perfect_depth valid.1 hit]
        simp only [Nat.cast_add, Nat.cast_one]
        linarith only [logNonnegative]
      | right hit =>
        have bound := layer_depth valid.2.2.1 hit positive
        have positiveMass := positive.trans_le (slot_le_mass hit (layer_nonnegative valid.2.2.1)).2
        have half : 2 * old.decode.mass ≤ (Icing.frozen carry old tail).decode.mass := by
          have thick := valid.2.2.2.2.1
          have carryMass := mass_nonnegative valid.2.1
          change 2 * old.decode.mass ≤ carry.mass + old.decode.mass + tail.decode.mass
          linarith only [thick, carryMass]
        have logarithm := ratio_log_double positiveMass positive half
        simp only [Nat.cast_add, Nat.cast_one] at bound ⊢
        linarith only [bound, logarithm]
    | right found =>
      have bound := icing_leaf_depth valid.2.2.2.1 found positive
      have positiveMass := positive.trans_le (slot_le_mass found (icing_nonnegative valid.2.2.2.1)).2
      have half : 2 * tail.decode.mass ≤ (Icing.frozen carry old tail).decode.mass := by
        have dominates := valid.2.2.2.2.2
        change 2 * tail.decode.mass ≤ carry.mass + old.decode.mass + tail.decode.mass
        linarith only [dominates]
      have logarithm := ratio_log_double positiveMass positive half
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [bound, logarithm]
termination_by sizeOf icing
end

/-- The Chocolate weighted-depth bound at level zero. -/
theorem weighted_depth {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.mass / weight) := by
  simpa only [Nat.cast_zero, zero_add] using layer_depth valid slot positive

end RotationBST.PopTart.Chocolate
