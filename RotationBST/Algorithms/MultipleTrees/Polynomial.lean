module

public import RotationBST.Algorithms.MultipleTrees.Sequence
public import RotationBST.Bounds.ConditionalEntropy.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Rounding a power of the universe size gives a legal cache capacity. The
exponent is capped at one because storing every successor already attains the
full-information bound. The choice depends only on `n` and `ε`. -/
theorem polynomial_capacity (n : Nat) (positive : 0 < n) (ε : ℝ) (exponent : 0 < ε) :
    ∃ capacity : Nat, 0 < capacity ∧ capacity ≤ n ∧
      (capacity : ℝ) ≤ 2 * (n : ℝ) ^ ε ∧
      (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) ≤ 1 / min ε 1 := by
  let a := min ε 1
  have aPositive : 0 < a := lt_min exponent (by norm_num)
  have aOne : a ≤ 1 := min_le_right _ _
  have aEpsilon : a ≤ ε := min_le_left _ _
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast positive
  have nPositive : (0 : ℝ) < n := by positivity
  have powerOne : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow nOne aPositive.le
  have powerFits : (n : ℝ) ^ a ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le nOne aOne
  let capacity := ⌈(n : ℝ) ^ a⌉₊
  have capacityPositive : 0 < capacity := by
    exact Nat.one_le_ceil_iff.mpr (by positivity)
  have capacityFits : capacity ≤ n := Nat.ceil_le.mpr powerFits
  have powerCapacity : (n : ℝ) ^ a ≤ capacity := Nat.le_ceil _
  have capacitySmall : (capacity : ℝ) ≤ 2 * (n : ℝ) ^ ε := by
    have rounded := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ a by positivity)
    have monotone := Real.rpow_le_rpow_of_exponent_le nOne aEpsilon
    change (capacity : ℝ) < (n : ℝ) ^ a + 1 at rounded
    linarith
  have logN : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) nOne
  have logCapacity : 0 ≤ Real.logb 2 capacity :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast capacityPositive)
  have logarithm : a * Real.logb 2 n ≤ Real.logb 2 capacity := by
    have bound := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show 0 < (n : ℝ) ^ a by positivity) powerCapacity
    simpa only [Real.logb_rpow_eq_mul_logb_of_pos nPositive] using bound
  refine ⟨capacity, capacityPositive, capacityFits, capacitySmall, ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + Real.logb 2 capacity) aPositive).mpr
  nlinarith

/-- Section 7's polynomial-space consequence of the multiple-tree tradeoff.
One integer capacity works for every request sequence on this universe. The
stored trees are then built from that sequence's empirical frequencies. -/
theorem polynomial_space (n : Nat) (positive : 0 < n) (ε : ℝ) (exponent : 0 < ε) :
    ∃ capacity : Nat, 0 < capacity ∧ capacity ≤ n ∧
      ∀ (p : Fin n) (xs : List (Fin n)), ∃ q k,
        LinkedSearch.Execution
          (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val)))
          p (xs.map Fin.val) q k ∧
        (k : ℝ) ≤ (6 / min ε 1) * (xs.length : ℝ) *
          (1 + ConditionalEntropy.entropy n p (xs.map Fin.val)) ∧
        ((build n capacity positive (LazyFinger.frequency p (xs.map Fin.val))).words : ℝ) ≤
          20 * (n : ℝ) ^ (1 + ε) := by
  obtain ⟨capacity, nonempty, fits, size, ratio⟩ := polynomial_capacity n positive ε exponent
  refine ⟨capacity, nonempty, fits, ?_⟩
  intro p xs
  obtain ⟨q, k, execution, time, space⟩ := sequence_tradeoff n capacity positive nonempty fits p xs
  have information : 0 ≤ ConditionalEntropy.cost n p (xs.map Fin.val) :=
    le_trans (by positivity) (ConditionalEntropy.length_le_cost n p (xs.map Fin.val))
  refine ⟨q, k, execution, ?_, ?_⟩
  · calc
      (k : ℝ) ≤ _ := time
      _ = 6 * ConditionalEntropy.cost n p (xs.map Fin.val) *
          ((1 + Real.logb 2 n) / (1 + Real.logb 2 capacity)) := by ring
      _ ≤ 6 * ConditionalEntropy.cost n p (xs.map Fin.val) * (1 / min ε 1) :=
        mul_le_mul_of_nonneg_left ratio (by positivity)
      _ = _ := by
        rw [ConditionalEntropy.cost_eq_length_mul_entropy, List.length_map]
        ring
  · have spaceReal :
        ((build n capacity positive (LazyFinger.frequency p (xs.map Fin.val))).words : ℝ) ≤
          10 * (n : ℝ) * capacity := by exact_mod_cast space
    calc
      _ ≤ 10 * (n : ℝ) * capacity := spaceReal
      _ ≤ 10 * (n : ℝ) * (2 * (n : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left size (by positivity)
      _ = 20 * (n : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
        ring

end RotationBST.MultipleTrees
