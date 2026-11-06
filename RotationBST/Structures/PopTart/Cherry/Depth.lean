module

public import RotationBST.Structures.PopTart.Cherry.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- The minimum fringe population of successive nonempty layers is geometric. -/
theorem layer_population {level : Nat} {layers : Layers} (valid : Valid level layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    2 ^ (level + layers.height) + 1 ≤ leafCount (layers.decode bottom) + 2 ^ level := by
  induction valid with
  | nil level => simp [Layers.height, Layers.decode, perfect_count base]
  | @one level a tail pa vt ih =>
    simp only [Layers.height, Layers.decode, leafCount, perfect_count pa]
    have twice : 2 ^ (level + 1) = 2 * 2 ^ level := by rw [pow_succ]; omega
    rw [show level + (tail.height + 1) = level + 1 + tail.height by omega]
    omega
  | @two level a b tail pa pb vt ih =>
    simp only [Layers.height, Layers.decode, leafCount, perfect_count pa, perfect_count pb]
    have twice : 2 ^ (level + 1) = 2 * 2 ^ level := by rw [pow_succ]; omega
    rw [show level + (tail.height + 1) = level + 1 + tail.height by omega]
    omega
  | @three level a b c tail pa pb pc vt ih =>
    simp only [Layers.height, Layers.decode, leafCount, perfect_count pa, perfect_count pb, perfect_count pc]
    have twice : 2 ^ (level + 1) = 2 * 2 ^ level := by rw [pow_succ]; omega
    rw [show level + (tail.height + 1) = level + 1 + tail.height by omega]
    omega

/-- At most three separator nodes and one extra crumb level are crossed per
layer. The bottom slot stays at depth zero when there are no layers. -/
theorem depth_height {level : Nat} {layers : Layers} (valid : Valid level layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    depth ≤ level + 4 * layers.height := by
  induction valid generalizing depth with
  | nil level =>
    have zero := perfect_depth base slot
    simp only [Layers.height]
    omega
  | @one level a tail pa vt ih =>
    cases slot with
    | left found => have eq := perfect_depth pa found; simp only [Layers.height]; omega
    | right found => have bound := ih found; simp only [Layers.height]; omega
  | @two level a b tail pa pb vt ih =>
    cases slot with
    | left found => have eq := perfect_depth pa found; simp only [Layers.height]; omega
    | right found =>
      cases found with
      | left hit => have eq := perfect_depth pb hit; simp only [Layers.height]; omega
      | right hit => have bound := ih hit; simp only [Layers.height]; omega
  | @three level a b c tail pa pb pc vt ih =>
    cases slot with
    | left found => have eq := perfect_depth pa found; simp only [Layers.height]; omega
    | right found =>
      cases found with
      | left hit => have eq := perfect_depth pb hit; simp only [Layers.height]; omega
      | right hit =>
        cases hit with
        | left last => have eq := perfect_depth pc last; simp only [Layers.height]; omega
        | right last => have bound := ih last; simp only [Layers.height]; omega

theorem height_log {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    (layers.height : ℝ) ≤ Real.logb 2 (leafCount (layers.decode bottom)) := by
  have population : 2 ^ layers.height ≤ leafCount (layers.decode bottom) := by
    have bound := layer_population valid base
    simpa only [Nat.zero_add, pow_zero, Nat.add_le_add_iff_right] using bound
  have realPopulation : (2 : ℝ) ^ layers.height ≤ (leafCount (layers.decode bottom) : ℝ) := by exact_mod_cast population
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) realPopulation
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

/-- The Cherry tree has logarithmic outer height, including all crumb leaves. -/
theorem depth_log {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    (depth : ℝ) ≤ 4 * Real.logb 2 (leafCount (layers.decode bottom)) := by
  have bound : (depth : ℝ) ≤ 4 * (layers.height : ℝ) := by
    have natural := depth_height valid base slot
    exact_mod_cast (by simpa only [Nat.zero_add] using natural)
  exact bound.trans (mul_le_mul_of_nonneg_left (height_log valid base) (by norm_num))

theorem worst_case {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    (layers.pushCost : ℝ) ≤ 10 * Real.logb 2 (leafCount (layers.decode bottom)) ∧
      (layers.popCost : ℝ) ≤ 6 * Real.logb 2 (leafCount (layers.decode bottom)) := by
  have height := height_log valid base
  have pushBound : (layers.pushCost : ℝ) ≤ 10 * (layers.height : ℝ) := by exact_mod_cast push_cost_height layers
  have popBound : (layers.popCost : ℝ) ≤ 6 * (layers.height : ℝ) := by exact_mod_cast pop_cost_height layers
  exact ⟨pushBound.trans (mul_le_mul_of_nonneg_left height (by norm_num)),
    popBound.trans (mul_le_mul_of_nonneg_left height (by norm_num))⟩

end RotationBST.PopTart.Cherry
