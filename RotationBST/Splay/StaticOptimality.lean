module

public import RotationBST.Splay.WeightedBound
public import RotationBST.Bounds.WeightedEntropy
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace RotationBST.Splay

theorem potential_lower_weights (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (t : Tree) (lo : Nat) :
    mass (fun i => Real.logb 2 (w i)) t lo ≤ potential w t lo := by
  induction t generalizing lo with
  | nil => exact le_rfl
  | node l r il ir =>
      have hl := il lo
      have hr := ir (lo + l.size + 1)
      have hk := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (hw (lo + l.size)) (weight_le_mass w hw l r lo)
      simp only [mass, potential] at hk ⊢
      linarith

theorem potential_upper (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (t : Tree) (lo : Nat)
    (W : ℝ) (hW : mass w t lo ≤ W) :
    potential w t lo ≤ (t.size : ℝ) * Real.logb 2 W := by
  induction t generalizing lo with
  | nil => simp [potential, Tree.size]
  | node l r il ir =>
      have hl := il lo ((mass_left_le w hw l r lo).trans hW)
      have hr := ir (lo + l.size + 1) ((mass_right_le w hw l r lo).trans hW)
      have hk := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (mass_pos w hw l r lo) hW
      simp only [potential, Tree.size, Nat.cast_add, Nat.cast_one]
      nlinarith

theorem mass_eq_finset (w : Nat → ℝ) (t : Tree) :
    mass w t 0 = ∑ i ∈ Finset.range t.size, w i := by
  rw [mass_eq_sum, ← List.range_eq_range']
  simpa only [List.toFinset_range] using (List.sum_toFinset w (l := List.range t.size) List.nodup_range).symm

theorem weightedSum_eq (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (W : ℝ) (hW : 0 < W)
    (xs : List Nat) :
    weightedSum w W xs = (xs.length : ℝ) +
      3 * (xs.map fun x => Real.logb 2 (W / w x)).sum := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih =>
      rw [weightedSum, ih]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons,
        Real.logb_div hW.ne' (hw x).ne']
      ring

/-- A sharper initialization allowance than the uniform minimum-weight bound. -/
theorem weighted_bound_finite (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size)
    (hW : 0 < mass w t 0) :
    (algorithm.cost t xs : ℝ) ≤ weightedSum w (mass w t 0) xs +
      ∑ i ∈ Finset.range t.size, Real.logb 2 (mass w t 0 / w i) := by
  have hb := weighted_run w hw [] t xs valid
  have hi := potential_upper w hw t 0 (mass w t 0) le_rfl
  have hf := potential_lower_weights w hw (algorithm.runFrom [] t xs).1 0
  have he := algorithm.execution [] t xs valid
  rw [← execution_mass_eq (fun i => Real.logb 2 (w i)) he] at hf
  have heq : ∑ i ∈ Finset.range t.size, Real.logb 2 (mass w t 0 / w i) =
      (t.size : ℝ) * Real.logb 2 (mass w t 0) - mass (fun i => Real.logb 2 (w i)) t 0 := by
    simp_rw [Real.logb_div hW.ne' (hw _).ne']
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [mass_eq_finset]
  rw [heq]
  unfold Algorithm.cost
  linarith

/-- Sleator--Tarjan static optimality without an initialization term when every
stored key occurs in the sequence (their Theorem 2 hypothesis). -/
theorem staticOptimality_all_accessed (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 4 * Bounds.staticCost t.size xs := by
  by_cases ht : t.size = 0
  · have hx : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => have := valid x (by simp); omega
    subst xs
    simp [Algorithm.totalCost, Algorithm.cost, Algorithm.runFrom, Bounds.staticCost]
  have hn : 0 < t.size := Nat.pos_of_ne_zero ht
  let w : Nat → ℝ := fun i => max 1 (xs.count i : ℝ)
  have hw : ∀ i, 0 < w i := by intro i; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hq (i : Nat) (hi : i < t.size) : (1 : ℝ) ≤ xs.count i := by
    exact_mod_cast (List.count_pos_iff.mpr (covers i hi))
  have hwe (i : Nat) (hi : i < t.size) : w i = (xs.count i : ℝ) := max_eq_right (hq i hi)
  have hmass : mass w t 0 = xs.length := by
    rw [mass_eq_finset]
    calc
      _ = ∑ i ∈ Finset.range t.size, (xs.count i : ℝ) :=
        Finset.sum_congr rfl (fun i hi => hwe i (Finset.mem_range.mp hi))
      _ = _ := Bounds.sum_count t.size xs valid
  have hm : (0 : ℝ) < xs.length := by
    have := hq 0 hn
    have hc : (xs.count 0 : ℝ) ≤ xs.length := by exact_mod_cast List.count_le_length
    linarith
  have hb := weighted_bound_finite w hw t xs valid (hmass ▸ hm)
  rw [hmass, weightedSum_eq w hw _ hm] at hb
  have hlogs : (xs.map fun x => Real.logb 2 ((xs.length : ℝ) / w x)).sum =
      ∑ i ∈ Finset.range t.size,
        (xs.count i : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count i) := by
    rw [← Bounds.sum_count_mul t.size xs _ valid]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hwe i (Finset.mem_range.mp hi)]
  rw [hlogs] at hb
  have hinit : (∑ i ∈ Finset.range t.size, Real.logb 2 ((xs.length : ℝ) / w i)) ≤
      ∑ i ∈ Finset.range t.size,
        (xs.count i : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi := Finset.mem_range.mp hi
    rw [hwe i hi]
    have hc : (xs.count i : ℝ) ≤ xs.length := by exact_mod_cast List.count_le_length
    have hp : (0 : ℝ) < xs.count i := lt_of_lt_of_le zero_lt_one (hq i hi)
    have hl : 0 ≤ Real.logb 2 ((xs.length : ℝ) / xs.count i) :=
      Real.logb_nonneg (by norm_num) ((le_div_iff₀ hp).mpr (by simpa using hc))
    nlinarith [hq i hi]
  simp only [Algorithm.totalCost, Nat.cast_add, Bounds.staticCost]
  nlinarith [Nat.cast_nonneg (α := ℝ) xs.length]

end RotationBST.Splay
