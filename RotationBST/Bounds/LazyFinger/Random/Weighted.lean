module

public import RotationBST.Bounds.LazyFinger.Random.Proofs
public import RotationBST.Bounds.LazyFinger.Random.SumBound
public import RotationBST.Bounds.WeightedFinger.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger
open Treap.Random RandomAnalysis

theorem exists_expected_log_bound (w : Nat → ℝ) (n : Nat) (hw : ∀ k < n, 0 < w k) :
    ∃ T : List Nat → Tree, (∀ xs, (T xs).size = n) ∧
      ∀ x y, x < n → y < n →
        average w (Finset.range n) (fun xs => (distance (T xs) x y : ℝ)) ≤
          4 * Real.log (WeightedFinger.mass w x y / min (w x) (w y)) := by
  obtain ⟨T, size, mean⟩ := exists_expected_distance w n 0 (by
    intro k hk
    exact hw k (by simpa using (Finset.mem_Ico.mp hk).2))
  have ordered (x y : Nat) (hx : x < n) (hy : y < n) (hxy : x ≤ y) :
      average w (Finset.range n) (fun xs => (distance (T xs) x y : ℝ)) ≤
        4 * Real.log (WeightedFinger.mass w x y / min (w x) (w y)) := by
    have hmean := mean x y (Nat.zero_le _) (by simpa using hx) (Nat.zero_le _) (by simpa using hy)
    simp only [Nat.zero_add, Nat.sub_zero, Nat.Ico_zero_eq_range] at hmean
    have hsum := sum_pairTerm_le w 0 n x y (Nat.zero_le _) hxy hy (by
      intro k hk; exact hw k (Finset.mem_Ico.mp hk).2)
    simp only [pairTerm, RandomAnalysis.segment, Finset.Ico_add_one_right_eq_Icc, Nat.Ico_zero_eq_range] at hsum
    rw [hmean]
    have hp : 0 < RandomAnalysis.segment w x (y + 1) := segment_pos w x (y + 1) (by omega) (by
      intro k hk; exact hw k (by have := (Finset.mem_Ico.mp hk).2; omega))
    have hmin : 0 < min (w x) (w y) := lt_min (hw x hx) (hw y hy)
    have hlogX := Real.log_le_log hmin (min_le_left (w x) (w y))
    have hlogY := Real.log_le_log hmin (min_le_right (w x) (w y))
    have hm : WeightedFinger.mass w x y = RandomAnalysis.segment w x (y + 1) := by
      simp only [WeightedFinger.mass, RandomAnalysis.segment, Finset.Ico_add_one_right_eq_Icc,
        min_eq_left hxy, max_eq_right hxy]
    rw [hm, Real.log_div hp.ne' hmin.ne']
    simp only [RandomAnalysis.segment, Finset.Ico_add_one_right_eq_Icc]
    linarith
  refine ⟨T, size, ?_⟩
  intro x y hx hy
  rcases le_total x y with h | h
  · exact ordered x y hx hy h
  · have hh := ordered y x hy hx h
    have he : (fun xs => (distance (T xs) x y : ℝ)) =
        (fun xs => (distance (T xs) y x : ℝ)) := by
      funext xs; rw [distance_symm]
    rw [he]
    simpa only [WeightedFinger.mass_symm w y x, min_comm (w y) (w x)] using hh

theorem log_le_logb_two (z : ℝ) (hz : 1 ≤ z) : Real.log z ≤ Real.logb 2 z := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  rw [Real.logb, le_div_iff₀ hp]
  nlinarith

/-- One random family works for every pair. Request charges and base-two
logarithms are now in exactly the public weighted-finger convention. -/
theorem exists_expected_charge_bound (w : Nat → ℝ) (n : Nat) (hw : ∀ k < n, 0 < w k) :
    ∃ T : List Nat → Tree, (∀ xs, (T xs).size = n) ∧
      ∀ x y, x < n → y < n →
        average w (Finset.range n) (fun xs => 1 + (distance (T xs) x y : ℝ)) ≤
          4 * WeightedFinger.charge w x y := by
  obtain ⟨T, size, hmean⟩ := exists_expected_log_bound w n hw
  refine ⟨T, size, ?_⟩
  intro x y hx hy
  have hw' : ∀ k ∈ Finset.range n, 0 < w k := fun k hk => hw k (Finset.mem_range.mp hk)
  rw [average_add, average_const w (Finset.range n) 1 hw']
  have hm : min (w x) (w y) ≤ WeightedFinger.mass w x y := by
    apply (min_le_left _ _).trans
    apply Finset.single_le_sum
    · intro k hk
      apply le_of_lt (hw k ?_)
      have hb := (Finset.mem_Icc.mp hk).2
      omega
    · exact Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have hp : 0 < min (w x) (w y) := lt_min (hw x hx) (hw y hy)
  have hr : 1 ≤ WeightedFinger.mass w x y / min (w x) (w y) :=
    (le_div_iff₀ hp).mpr (by simpa using hm)
  have hlog := log_le_logb_two _ hr
  have hh := hmean x y hx hy
  unfold WeightedFinger.charge
  linarith

/-- Weights-to-tree direction for a whole sequence. The selected tree may
 depend on the sequence, but is fixed throughout its execution. -/
theorem exists_tree_for_weights (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (hw : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t.size = n ∧
      (costFrom t p xs : ℝ) ≤ 4 * WeightedFinger.costFrom w p xs := by
  obtain ⟨T, size, hmean⟩ := exists_expected_charge_bound w n hw
  have hw' : ∀ k ∈ Finset.range n, 0 < w k := fun k hk => hw k (Finset.mem_range.mp hk)
  have bound : average w (Finset.range n) (fun order => (costFrom (T order) p xs : ℝ)) ≤
      4 * WeightedFinger.costFrom w p xs := by
    induction xs generalizing p with
    | nil => simp only [costFrom, WeightedFinger.costFrom, Nat.cast_zero, average_zero, mul_zero, le_refl]
    | cons x xs ih =>
      have hx : x < n := valid x (by simp)
      have hv : ∀ y ∈ xs, y < n := fun y hy => valid y (by simp [hy])
      have ht := ih x hx hv
      have hh := hmean p x hp hx
      simp only [costFrom, Nat.cast_add, Nat.cast_one, WeightedFinger.costFrom]
      rw [average_add]
      linarith
  obtain ⟨order, _, ho⟩ := exists_order_le_average w (Finset.range n)
    (fun order => (costFrom (T order) p xs : ℝ)) hw'
  exact ⟨T order, size order, ho.trans bound⟩

end RotationBST.LazyFinger
