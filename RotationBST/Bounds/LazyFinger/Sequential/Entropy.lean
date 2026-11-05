module

public import RotationBST.Bounds.LazyFinger.Sequential.Sequence
public import RotationBST.Bounds.StaticTree.Comparison
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Uniform frequencies give the exact entropy benchmark. Repeating the scan
changes its length but not its per-request logarithmic charge. -/
theorem scans_entropy (n rounds : Nat) :
    Bounds.staticCost n (scans n rounds) = (rounds * n : Nat) * (1 + Real.logb 2 (n : ℝ)) := by
  by_cases hr : rounds = 0
  · subst rounds
    simp [scans, Bounds.staticCost]
  · have hr' : (rounds : ℝ) ≠ 0 := by exact_mod_cast hr
    unfold Bounds.staticCost
    rw [scans_length]
    have hs : (∑ x ∈ Finset.range n,
        ((scans n rounds).count x : ℝ) * Real.logb 2 ((rounds * n : Nat) / ((scans n rounds).count x : ℝ))) =
        ∑ _ ∈ Finset.range n, (rounds : ℝ) * Real.logb 2 (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [scans_count, Finset.mem_range.mp hx, ↓reduceIte]
      push_cast
      rw [mul_div_cancel_left₀ _ hr']
    rw [hs]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
    ring

/-- Root-finger cost is logarithmic per scan request on every fixed tree. -/
theorem scans_root_lower (t : Tree) (rounds : Nat) :
    (rounds * t.size : Nat) * (1 + Real.logb 2 (t.size : ℝ)) ≤
      3 * (StaticTree.cost t (scans t.size rounds) : ℝ) := by
  rw [← scans_entropy]
  exact StaticTree.entropy_le_cost t _ (scans_valid t.size rounds)

/-- For power-of-two universes the logarithmic lower bound has an entirely
natural-number statement. -/
theorem scans_root_power_lower (t : Tree) (k rounds : Nat) (ht : t.size = 2 ^ k) :
    (k + 1) * (rounds * t.size) ≤ 3 * StaticTree.cost t (scans t.size rounds) := by
  have h := scans_root_lower t rounds
  have hl : Real.logb 2 (t.size : ℝ) = k := by
    rw [ht, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
    norm_num
  rw [hl] at h
  have he : ((k + 1) * (rounds * t.size) : Nat) ≤ 3 * StaticTree.cost t (scans t.size rounds) := by
    exact_mod_cast (show ((k : ℝ) + 1) * (rounds * t.size : Nat) ≤
      3 * (StaticTree.cost t (scans t.size rounds) : ℝ) by nlinarith [h])
  exact he

end RotationBST.LazyFinger
