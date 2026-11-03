module

public import RotationBST.Bounds.Abstract
public import RotationBST.Bounds.Implications.Gaps
public import RotationBST.Bounds.Implications.LogSum

@[expose] public section

namespace RotationBST.Bounds

theorem gaps_log_step (ages : Nat → Nat) (x y : Nat) (xs : List Nat) :
    ((gaps y (ages y) (x :: xs)).map fun g : Nat => Real.logb 2 g).sum =
      (if y = x then Real.logb 2 (ages x + 1 : Nat) else 0) +
        ((gaps y (nextAge ages x y) xs).map fun g : Nat => Real.logb 2 g).sum := by
  by_cases h : y = x
  · subst y; simp [gaps, nextAge]
  · simp [gaps, nextAge, h, Ne.symm h]

/-- Group the chronological gap charges by the key whose access ends each gap. -/
theorem gapSum_group (n : Nat) (ages : Nat → Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    gapSum ages xs = ∑ y ∈ Finset.range n,
      ((gaps y (ages y) xs).map fun g : Nat => Real.logb 2 g).sum := by
  induction xs generalizing ages with
  | nil => simp [gapSum, gaps]
  | cons x xs ih =>
      have hx := valid x (by simp)
      have hv : ∀ y ∈ xs, y < n := by intro y hy; exact valid y (by simp [hy])
      rw [gapSum, ih (nextAge ages x) hv]
      simp only [gaps_log_step, Finset.sum_add_distrib]
      simp [hx]

theorem gapSum_le_entropy (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    gapSum (fun _ => 0) xs ≤ ∑ x ∈ Finset.range n,
      (xs.count x : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count x) := by
  rw [gapSum_group n _ xs valid]
  apply Finset.sum_le_sum
  intro x _
  have hs : ((gaps x 0 xs).sum : ℝ) ≤ xs.length := by
    exact_mod_cast (by simpa using gaps_sum_le x 0 xs)
  have h := logSum_le (gaps x 0 xs) (gaps_pos x 0 xs) xs.length hs
  simpa only [gaps_length] using h

theorem logb_nat_nonneg (n : Nat) : 0 ≤ Real.logb 2 n := by
  by_cases hn : n = 0
  · subst n; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- The working-set sum is at most frequency entropy plus the first-use allowance.
This is a sequence inequality, independent of any BST algorithm. -/
theorem workingSet_le_static (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (workingSetSum n [] xs : ℝ) ≤ staticCost n xs +
      (n : ℝ) * (1 + (n.log2 : ℝ)) := by
  have hw := workingSet_le_gaps n [] xs
  have hage : age [] = fun _ => 0 := by funext x; simp [age]
  rw [hage] at hw
  have hg := gapSum_le_entropy n xs valid
  have hn : (newCount [] xs : ℝ) ≤ n := by exact_mod_cast newCount_le n xs valid
  have hp := mul_le_mul_of_nonneg_right hn (logb_nat_nonneg n)
  have hlog := mul_le_mul_of_nonneg_left (Recency.logb_nat_le n) (Nat.cast_nonneg (α := ℝ) n)
  unfold staticCost
  nlinarith

/-- Entropy terms are nonnegative because no key occurs more often than the
length of the sequence. -/
theorem length_le_staticCost (n : Nat) (xs : List Nat) : (xs.length : ℝ) ≤ staticCost n xs := by
  have h : 0 ≤ ∑ x ∈ Finset.range n,
      (xs.count x : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count x) := by
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : xs.count x = 0
    · simp [hx]
    · have hpos : (0 : ℝ) < xs.count x := by exact_mod_cast Nat.pos_of_ne_zero hx
      have hle : (xs.count x : ℝ) ≤ xs.length := by exact_mod_cast List.count_le_length
      have hone : (1 : ℝ) ≤ (xs.length : ℝ) / xs.count x := (le_div_iff₀ hpos).mpr (by simpa using hle)
      exact mul_nonneg hpos.le (Real.logb_nonneg (by norm_num) hone)
  unfold staticCost
  linarith

end RotationBST.Bounds
