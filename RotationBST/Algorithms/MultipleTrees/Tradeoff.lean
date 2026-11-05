module

public import RotationBST.Algorithms.MultipleTrees.Queries
public import RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

theorem rowTotal_eq_sum (n : Nat) (frequency : Nat → Nat → Nat) (p : Nat) :
    ConditionalEntropy.rowTotal n frequency p = ((List.range n).map (frequency p)).sum := by
  simpa only [ConditionalEntropy.rowTotal, List.toFinset_range] using
    (List.sum_toFinset (frequency p) (l := List.range n) List.nodup_range)

/-- The per-request space/time tradeoff, normalized so capacity one and
deterministic transitions remain meaningful. All charged searches and links
are those of the executable linked-search request. -/
theorem request_tradeoff (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) (fits : capacity ≤ n) (p x : Fin n) (observed : 0 < frequency p x) :
    ((LinkedSearch.request (build n capacity positive frequency) p x).2 : ℝ) ≤
      6 * (1 + Real.logb 2 ((ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x)) *
        (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) := by
  let I := Real.logb 2 ((ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x)
  let u := Real.logb 2 (n : ℝ)
  let v := Real.logb 2 (capacity : ℝ)
  let k := (LinkedSearch.request (build n capacity positive frequency) p x).2
  have nPositive : (0 : ℝ) < n := by exact_mod_cast positive
  have dPositive : (0 : ℝ) < capacity := by exact_mod_cast nonempty
  have uNonneg : 0 ≤ u := Real.logb_nonneg (by norm_num) (by exact_mod_cast positive)
  have vNonneg : 0 ≤ v := Real.logb_nonneg (by norm_num) (by exact_mod_cast nonempty)
  have vu : v ≤ u := Real.logb_le_logb_of_le (by norm_num) dPositive (by exact_mod_cast fits)
  have fPositive : (0 : ℝ) < frequency p x := by exact_mod_cast observed
  have entry : frequency p x ≤ ConditionalEntropy.rowTotal n frequency p :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr x.isLt)
  have ratio : (1 : ℝ) ≤ (ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x := by
    apply (le_div_iff₀ fPositive).mpr
    simpa only [one_mul] using (show (frequency p x : ℝ) ≤ _ by exact_mod_cast entry)
  have iNonneg : 0 ≤ I := Real.logb_nonneg (by norm_num) ratio
  have denominator : 0 < 1 + v := by linarith
  change (k : ℝ) ≤ 6 * (1 + I) * (1 + u) / (1 + v)
  apply (le_div_iff₀ denominator).mpr
  by_cases stored : x.val ∈ selected n capacity (frequency p)
  · have bound := request_hit_weighted n capacity positive frequency p x stored observed
    rw [← rowTotal_eq_sum] at bound
    have divide : 3 * (ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x =
        3 * ((ConditionalEntropy.rowTotal n frequency p : ℝ) / frequency p x) := by ring
    rw [divide, Real.logb_mul (by norm_num) (by positivity)] at bound
    have three : Real.logb 2 3 ≤ (2 : ℝ) := by
      have bound := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 ^ 2)
      simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one, Nat.cast_ofNat] using bound
    have small : (k : ℝ) ≤ 6 * (1 + I) := by
      change (k : ℝ) ≤ Real.logb 2 3 + I + 2 at bound
      linarith
    calc
      (k : ℝ) * (1 + v) ≤ 6 * (1 + I) * (1 + v) := mul_le_mul_of_nonneg_right small (by linarith)
      _ ≤ 6 * (1 + I) * (1 + u) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have miss := omitted_information n capacity (frequency p) x fits nonempty x.isLt stored observed
    rw [← rowTotal_eq_sum] at miss
    change v ≤ I at miss
    have bound := request_uniform n capacity positive frequency nonempty p x
    rw [Nat.min_eq_left fits, Real.logb_mul (by norm_num) (ne_of_gt dPositive),
      Real.logb_mul (by norm_num) (ne_of_gt nPositive),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at bound
    change (k : ℝ) ≤ 1 + v + (1 + u) + 4 at bound
    have small : (k : ℝ) ≤ 6 * (1 + u) := by linarith
    calc
      (k : ℝ) * (1 + v) ≤ 6 * (1 + u) * (1 + v) := mul_le_mul_of_nonneg_right small (by linarith)
      _ ≤ 6 * (1 + u) * (1 + I) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 6 * (1 + I) * (1 + u) := by ring

end RotationBST.MultipleTrees
