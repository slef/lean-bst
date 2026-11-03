module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace RotationBST.Splay

/-- The two disjoint masses inequality behind the splay access lemma. -/
theorem log_pair_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ c) :
    Real.logb 2 a + Real.logb 2 b ≤ 2 * Real.logb 2 c - 2 := by
  have hc : 0 < c := by linarith
  have hm : a * b ≤ (c / 2) ^ 2 := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ c + a + b by linarith)]
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (mul_pos ha hb) hm
  rw [Real.logb_mul ha.ne' hb.ne', Real.logb_pow,
    Real.logb_div hc.ne' (by norm_num), Real.logb_self_eq_one (by norm_num)] at hh
  norm_num at hh
  linarith

/-- The single rotation estimate. `x` is the old focused mass, `y` the
new mass of its former parent, and `z` their common total mass. -/
theorem zig_inequality {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxz : x ≤ z) (hyz : y ≤ z) :
    1 + Real.logb 2 y - Real.logb 2 x ≤
      3 * (Real.logb 2 z - Real.logb 2 x) + 1 := by
  have h₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hxz
  have h₂ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hy hyz
  linarith

/-- The zig-zig estimate, after canceling the unchanged total-root rank. -/
theorem zigzig_inequality {x y y' z' z : ℝ}
    (hx : 0 < x) (hy' : 0 < y') (hz' : 0 < z')
    (hxy : x ≤ y) (hy'z : y' ≤ z) (hdisjoint : x + z' ≤ z) :
    2 + Real.logb 2 y' + Real.logb 2 z' - Real.logb 2 x - Real.logb 2 y ≤
      3 * (Real.logb 2 z - Real.logb 2 x) := by
  have h₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hxy
  have h₂ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hy' hy'z
  have h₃ := log_pair_le hx hz' hdisjoint
  linarith

/-- The zig-zag estimate. The two new children have disjoint key sets. -/
theorem zigzag_inequality {x y y' z' z : ℝ}
    (hx : 0 < x) (hy' : 0 < y') (hz' : 0 < z')
    (hxy : x ≤ y) (hxz : x ≤ z) (hdisjoint : y' + z' ≤ z) :
    2 + Real.logb 2 y' + Real.logb 2 z' - Real.logb 2 x - Real.logb 2 y ≤
      3 * (Real.logb 2 z - Real.logb 2 x) := by
  have h₁ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hxy
  have h₂ := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx hxz
  have h₃ := log_pair_le hy' hz' hdisjoint
  linarith

end RotationBST.Splay
