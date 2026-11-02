module

public import RotationBST.Bounds.Entropy
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace RotationBST.Bounds

theorem sum_count_mul (n : Nat) (xs : List Nat) (f : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < n) :
    ∑ x ∈ Finset.range n, (xs.count x : ℝ) * f x = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := valid x (by simp)
      have hv : ∀ y ∈ xs, y < n := by intro y hy; exact valid y (by simp [hy])
      have hc (y : Nat) : ((x :: xs).count y : ℝ) * f y =
          (if y = x then f x else 0) + (xs.count y : ℝ) * f y := by
        by_cases h : y = x
        · subst y; simp; ring
        · simp [h, Ne.symm h]
      simp_rw [hc]
      rw [Finset.sum_add_distrib, ih hv]
      simp [hx]

theorem sum_count (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∑ x ∈ Finset.range n, (xs.count x : ℝ) = xs.length := by
  simpa using sum_count_mul n xs (fun _ => 1) valid

/-- The tangent-line inequality for one entropy term, including zero frequency. -/
theorem entropy_term_le (m q w W : ℝ) (hm : 0 ≤ m) (hq : 0 ≤ q) (hqm : q ≤ m)
    (hw : 0 < w) (hW : 0 < W) :
    q * Real.logb 2 (m / q) ≤ q * Real.logb 2 (W / w) +
      (m / W * w - q) / Real.log 2 := by
  by_cases hq0 : q = 0
  · subst q
    simp only [zero_mul, sub_zero, zero_add]
    positivity
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hmpos : 0 < m := lt_of_lt_of_le hqpos hqm
    have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos hmpos hw) (mul_pos hqpos hW))
    rw [Real.log_div (mul_ne_zero hmpos.ne' hw.ne') (mul_ne_zero hqpos.ne' hW.ne'),
      Real.log_mul hmpos.ne' hw.ne', Real.log_mul hqpos.ne' hW.ne'] at h
    have hmul := mul_le_mul_of_nonneg_left h hq
    have he : q * (m * w / (q * W) - 1) = m / W * w - q := by
      field_simp
    rw [he] at hmul
    have hnat : q * Real.log (m / q) ≤ q * Real.log (W / w) + (m / W * w - q) := by
      rw [Real.log_div hmpos.ne' hqpos.ne', Real.log_div hW.ne' hw.ne']
      nlinarith
    have hb := div_le_div_of_nonneg_right hnat (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    simpa only [Real.logb, add_div, mul_div_assoc] using hb

/-- Frequency entropy is bounded by the code lengths supplied by any positive
weight assignment with total mass at most `W`. -/
theorem entropy_le_weighted (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n)
    (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (W : ℝ) (hW : 0 < W)
    (hsum : ∑ i ∈ Finset.range n, w i ≤ W) :
    ∑ x ∈ Finset.range n, (xs.count x : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count x) ≤
      ∑ x ∈ Finset.range n, (xs.count x : ℝ) * Real.logb 2 (W / w x) := by
  have hp (x : Nat) : (xs.count x : ℝ) ≤ xs.length := by exact_mod_cast List.count_le_length
  have h := Finset.sum_le_sum (s := Finset.range n) (fun x _ =>
    entropy_term_le xs.length (xs.count x) (w x) W (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (hp x) (hw x) hW)
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_count n xs valid] at h
  have herr := mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg (α := ℝ) xs.length) hW.le)
  rw [div_mul_cancel₀ _ hW.ne'] at herr
  have he : ((xs.length : ℝ) / W * (∑ x ∈ Finset.range n, w x) - xs.length) / Real.log 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  linarith

end RotationBST.Bounds
