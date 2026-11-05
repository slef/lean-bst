module

public import RotationBST.Bounds.LazyFinger.Optimal
public import RotationBST.Bounds.LazyFinger.Initialization
public import RotationBST.Bounds.LazyFinger.Weights
public import RotationBST.Bounds.LazyFinger.Random.Weighted
public import RotationBST.Bounds.WeightedFinger.Optimization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Exact constant-factor comparison of the optimized benchmarks, with the
same specified initial key. The tree minimum is attained; the weight infimum
need not be. -/
theorem optimal_from_characterization (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    WeightedFinger.optimalCostFrom n p xs ≤ 3 * (optimalCostFrom n p xs : ℝ) ∧
      (optimalCostFrom n p xs : ℝ) ≤ 4 * WeightedFinger.optimalCostFrom n p xs := by
  constructor
  · obtain ⟨t, size, hcost⟩ := optimalCostFrom_attained n p xs
    obtain ⟨w, hw, _, bound⟩ := exists_weights_for_tree t
    have hw' : ∀ k < n, 0 < w k := fun k _ => hw k
    have hb := bound p xs (by simpa [size] using hp) (by simpa [size] using valid)
    have hi := WeightedFinger.optimalCostFrom_le w n p xs hw' hp valid
    rw [hcost] at hb
    exact hi.trans hb
  · have hi : (optimalCostFrom n p xs : ℝ) / 4 ≤ WeightedFinger.optimalCostFrom n p xs := by
      apply WeightedFinger.le_optimalCostFrom
      intro w hw
      obtain ⟨t, size, hcost⟩ := exists_tree_for_weights w n p xs hw hp valid
      have ht := optimalCostFrom_le t p xs
      rw [size] at ht
      have ht' : (optimalCostFrom n p xs : ℝ) ≤ costFrom t p xs := by exact_mod_cast ht
      linarith
    linarith

/-- Optimizing the tree does not increase the one-time initialization penalty. -/
theorem optimal_initialization_bounds (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    optimalCostFrom n p xs ≤ n + optimalCost n xs ∧
      optimalCost n xs ≤ n + optimalCostFrom n p xs := by
  constructor
  · obtain ⟨t, size, hcost⟩ := optimalCost_attained n xs
    have h := (initialization_bounds t p xs (by simpa [size] using hp)
      (by simpa [size] using valid)).1
    have hi := optimalCostFrom_le t p xs
    rw [size] at hi
    rw [size, hcost] at h
    exact hi.trans h
  · obtain ⟨t, size, hcost⟩ := optimalCostFrom_attained n p xs
    have h := (initialization_bounds t p xs (by simpa [size] using hp)
      (by simpa [size] using valid)).2
    have hi := optimalCost_le t xs
    rw [size] at hi
    rw [size, hcost] at h
    exact hi.trans h

/-- Root-start form of the characterization, with the additive initialization
terms written explicitly rather than hidden in asymptotic notation. -/
theorem optimal_root_characterization (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    WeightedFinger.optimalCostFrom n p xs ≤ 3 * ((optimalCost n xs : ℝ) + n) ∧
      (optimalCost n xs : ℝ) ≤ n + 4 * WeightedFinger.optimalCostFrom n p xs := by
  obtain ⟨hW, hT⟩ := optimal_from_characterization n p xs hp valid
  obtain ⟨h₁, h₂⟩ := optimal_initialization_bounds n p xs hp valid
  have h₁' : (optimalCostFrom n p xs : ℝ) ≤ n + (optimalCost n xs : ℝ) := by exact_mod_cast h₁
  have h₂' : (optimalCost n xs : ℝ) ≤ n + (optimalCostFrom n p xs : ℝ) := by exact_mod_cast h₂
  constructor <;> linarith

/-- The optimized root-start and weighted benchmarks, each augmented by `n`,
are within factor four of one another. This is a startup-explicit version of
the lazy-finger characterization, with normalized request charges. -/
theorem characterization_with_startup (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) + n ≤ 4 * (WeightedFinger.optimalCostFrom n p xs + n) ∧
      WeightedFinger.optimalCostFrom n p xs + n ≤ 4 * ((optimalCost n xs : ℝ) + n) := by
  obtain ⟨hW, hT⟩ := optimal_root_characterization n p xs hp valid
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ optimalCost n xs := Nat.cast_nonneg _
  constructor <;> linarith

/-- For sequences at least as long as the key universe, request charges absorb
the startup terms, giving a purely multiplicative characterization. -/
theorem characterization_long (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (long : n ≤ xs.length) :
    WeightedFinger.optimalCostFrom n p xs ≤ 6 * (optimalCost n xs : ℝ) ∧
      (optimalCost n xs : ℝ) ≤ 5 * WeightedFinger.optimalCostFrom n p xs := by
  obtain ⟨hW, hT⟩ := optimal_root_characterization n p xs hp valid
  have hm : (n : ℝ) ≤ xs.length := by exact_mod_cast long
  have hL : (xs.length : ℝ) ≤ optimalCost n xs := by exact_mod_cast length_le_optimalCost n xs
  have hF := WeightedFinger.length_le_optimalCostFrom n p xs hp valid
  constructor <;> linarith

end RotationBST.LazyFinger
