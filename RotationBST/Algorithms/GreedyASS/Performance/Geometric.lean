module

public import RotationBST.Algorithms.GreedyASS.Reference.Conversion.Sequence
public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Stream
public import RotationBST.Bounds.LazyFinger.Abstract
public import RotationBST.Bounds.WeightedFinger.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Performance
open Reference

/-- GreedyASS is competitive with every ordinary static BST and every
initial finger. Neither the tree nor the finger is an input to the sweep. -/
theorem lazy_from (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.costFrom t p xs + 15 * t.size := by
  have population := Conversion.population t (by omega)
  have geometric := Potential.Amortized.cost (Conversion.convert t) 0 xs (by simpa [population] using valid)
  have comparison := Conversion.cost_from t p xs hp valid
  rw [population] at geometric
  omega

theorem lazy_tree (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.cost t xs + 15 * t.size := by
  cases t with
  | nil =>
    have empty : xs = [] := List.eq_nil_iff_forall_not_mem.mpr (by simpa [Tree.size] using valid)
    subst xs
    simp [rowCost]
  | node l r => exact lazy_from (.node l r) l.size xs (by simp [Tree.size]; omega) valid

/-- Theorem 4.1 in the geometric model, with the minimum over ordinary
BST shapes attained and initialization charged once. -/
theorem lazy_optimal (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.optimalCost n xs + 15 * n := by
  obtain ⟨t, size, optimum⟩ := LazyFinger.Results.optimal_attained n xs
  have bound := lazy_tree t xs (by simpa [size] using valid)
  simpa only [size, optimum] using bound

theorem lazy_optimal_from (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.optimalCostFrom n p xs + 15 * n := by
  obtain ⟨t, size, optimum⟩ := LazyFinger.Results.optimal_from_attained n p xs
  have bound := lazy_from t p xs (by simpa [size] using hp) (by simpa [size] using valid)
  simpa only [size, optimum] using bound

/-- Theorem 4.2, retaining an infimum over positive weights rather than
assuming that an optimal weighting exists. Request charges normalize
repeated keys and a valid predecessor specifies the first weighted charge. -/
theorem weighted_optimal (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * WeightedFinger.optimalCostFrom n p xs + 15 * n := by
  have geometric : (rowCost greedySweep 0 ∅ xs : ℝ) ≤
      120 * (LazyFinger.optimalCostFrom n p xs : ℝ) + 15 * n := by
    exact_mod_cast lazy_optimal_from n p xs hp valid
  have comparison := (LazyFinger.Results.characterization_from n p xs hp valid).2
  linarith

/-- The same sweep satisfies the bound for every positive weighting. -/
theorem weighted (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (positive : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * WeightedFinger.costFrom w p xs + 15 * n := by
  have bound := weighted_optimal n p xs hp valid
  have comparison := WeightedFinger.Results.optimal_le w n p xs positive hp valid
  linarith

end RotationBST.Geometric.GreedyASS.Performance
