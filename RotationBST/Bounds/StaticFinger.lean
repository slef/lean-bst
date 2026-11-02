module

public import RotationBST.Bounds.WeightedEntropy
public import RotationBST.Bounds.Properties

@[expose] public section

namespace RotationBST.Bounds

noncomputable def fingerWeight (f x : Nat) : ℝ := (((Nat.dist x f : ℝ) + 1) ^ 2)⁻¹

theorem fingerWeight_pos (f x : Nat) : 0 < fingerWeight f x := by
  unfold fingerWeight
  positivity

theorem squareSum_finset (n : Nat) :
    ∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)⁻¹ = Recency.squareSum n := by
  simpa only [List.toFinset_range, Recency.squareSum] using
    List.sum_toFinset (fun i : Nat => (((i : ℝ) + 1) ^ 2)⁻¹) (l := List.range n) List.nodup_range

theorem fingerWeight_left (f : Nat) :
    ∑ i ∈ Finset.range (f + 1), fingerWeight f i = Recency.squareSum (f + 1) := by
  have hd : ∑ i ∈ Finset.range (f + 1), fingerWeight f i =
      ∑ i ∈ Finset.range (f + 1), ((((f - i : Nat) : ℝ) + 1) ^ 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ f := by have := Finset.mem_range.mp hi; omega
    simp only [fingerWeight, Nat.dist_eq_sub_of_le hi']
  rw [hd]
  have href := Finset.sum_range_reflect (fun i : Nat => (((i : ℝ) + 1) ^ 2)⁻¹) (f + 1)
  simp only [Nat.add_sub_cancel] at href
  rw [href, squareSum_finset]

theorem fingerWeight_right (f m : Nat) :
    ∑ i ∈ Finset.range m, fingerWeight f (f + 1 + i) ≤ Recency.squareSum m := by
  rw [← squareSum_finset]
  apply Finset.sum_le_sum
  intro i _
  have hd : Nat.dist (f + 1 + i) f = i + 1 := by
    rw [Nat.dist_eq_sub_of_le_right (by omega)]; omega
  simp only [fingerWeight, hd, Nat.cast_add, Nat.cast_one]
  apply inv_anti₀ (by positivity)
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  nlinarith

/-- Reciprocal squared distance weights have bounded total mass uniformly in
both the universe size and the finger position. -/
theorem fingerWeight_sum (n f : Nat) : ∑ i ∈ Finset.range n, fingerWeight f i ≤ 4 := by
  by_cases h : n ≤ f + 1
  · have hs : ∑ i ∈ Finset.range n, fingerWeight f i ≤
        ∑ i ∈ Finset.range (f + 1), fingerWeight f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
        (fun i _ _ => (fingerWeight_pos f i).le)
    rw [fingerWeight_left] at hs
    have := Recency.squareSum_le_two (f + 1)
    linarith
  · have hn : n = (f + 1) + (n - (f + 1)) := by omega
    rw [hn, Finset.sum_range_add, fingerWeight_left]
    have hr := fingerWeight_right f (n - (f + 1))
    have h₁ := Recency.squareSum_le_two (f + 1)
    have h₂ := Recency.squareSum_le_two (n - (f + 1))
    linarith

theorem finger_log_weight (f x : Nat) :
    Real.logb 2 (4 / fingerWeight f x) = 2 + 2 * Real.logb 2 (Nat.dist x f + 1 : Nat) := by
  have hfour : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [Real.logb_div (by norm_num) (fingerWeight_pos f x).ne', hfour]
  simp only [fingerWeight, Real.logb_inv, Real.logb_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  ring

theorem length_le_fingerCost (f : Nat) (xs : List Nat) : (xs.length : ℝ) ≤ fingerCost f xs := by
  induction xs with
  | nil => simp [fingerCost]
  | cons x xs ih =>
      have h := logb_nat_nonneg (Nat.dist x f + 1)
      simp only [Nat.cast_add, Nat.cast_one] at h
      simp only [fingerCost, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one] at ih ⊢
      linarith

/-- Static entropy is at most three times the fixed-finger bound. -/
theorem static_le_finger (n f : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    staticCost n xs ≤ 3 * fingerCost f xs := by
  have h := entropy_le_weighted n xs valid (fingerWeight f) (fingerWeight_pos f) 4
    (by norm_num) (fingerWeight_sum n f)
  rw [sum_count_mul n xs (fun x => Real.logb 2 (4 / fingerWeight f x)) valid] at h
  have he : (xs.map fun x : Nat => Real.logb 2 (4 / fingerWeight f x)).sum = 2 * fingerCost f xs := by
    have aux (ls : List Nat) :
        (ls.map fun x : Nat => Real.logb 2 (4 / fingerWeight f x)).sum = 2 * fingerCost f ls := by
      induction ls with
      | nil => simp [fingerCost]
      | cons x ls ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [finger_log_weight, ih]
          simp only [fingerCost, List.map_cons, List.sum_cons]
          ring
    exact aux xs
  rw [he] at h
  have hl := length_le_fingerCost f xs
  unfold staticCost
  linarith

end RotationBST.Bounds
