module

public import RotationBST.Structures.PopTart.Vanilla.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Vanilla

/-- The mass doubles at each right-spine step. A fringe leaf at depth `d`
therefore has `2^d` times its weight bounded by twice the total weight. -/
theorem depth_mass {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) :
    (2 : ℝ) ^ depth * weight ≤ 2 * stack.mass := by
  induction valid generalizing subtree weight depth with
  | leaf t w pos =>
    cases slot
    simp only [pow_zero, one_mul, WeightedTree.mass]
    linarith
  | @push tail t w tailValid dominates ih =>
    cases slot with
    | left found =>
      cases found
      have tailNonnegative := WeightedTree.mass_nonnegative (nonnegative tailValid)
      simp only [Nat.zero_add, pow_one, WeightedTree.mass]
      linarith
    | right found =>
      have smaller := ih found
      simp only [pow_succ, WeightedTree.mass]
      nlinarith only [smaller, dominates]

/-- Lemma 1 of De-amortizing Binary Search Trees: every positive-weight
fringe slot in the Vanilla pop-tart has depth at most `1 + log₂(W/w)`. -/
theorem depth_log {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) (slotPositive : 0 < weight) :
    (depth : ℝ) ≤ 1 + Real.logb 2 (stack.mass / weight) := by
  have totalPositive := slotPositive.trans_le (WeightedTree.slot_le_mass slot (nonnegative valid)).2
  have ratio : (2 : ℝ) ^ depth ≤ 2 * (stack.mass / weight) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ slotPositive).mpr (depth_mass valid slot)
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  rw [Real.logb_pow, Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
    (ne_of_gt (div_pos totalPositive slotPositive))] at logarithm
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

/-- The weighted-depth bound is realized in the same physical pointer tree
when the fringe slot contains a nonempty frozen subtree. -/
theorem access_slot {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) (slotPositive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = stack.tree ∧
      Pointer.Trace ⟨stack.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 1 + Real.logb 2 (stack.mass / weight) := by
  obtain ⟨cs, length, plugged, trace⟩ := WeightedTree.slot_trace slot nonempty
  exact ⟨cs, length, plugged, trace, depth_log valid slot slotPositive⟩

end RotationBST.PopTart.Vanilla
