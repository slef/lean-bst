module

public import RotationBST.Bounds.LazyFinger.Consequences.Abstract
public import RotationBST.Algorithms.OptimalLazyFinger.Work.Abstract
public import RotationBST.Bounds.StaticTree.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.LazyFingerConsequences

-- Zero-frequency keys remain present, and the sole observed key is the root.
example : WeightedSearch.build [0, 0, 7, 0] =
    Tree.node (.node .nil (.node .nil .nil)) (.node .nil .nil) := by decide

example : ∃ t : Tree, t.size = 4 ∧ (StaticTree.cost t [2, 2, 2] : ℝ) ≤ 3 := by
  have result := StaticTree.Results.entropy_upper_bound 4 [2, 2, 2] (by simp)
  norm_num [Bounds.staticCost, Finset.sum_range_succ] at result
  exact_mod_cast result

-- The predecessor is counted only once; repeated accesses cost a unit each.
example : Bounds.dynamicFingerCostFrom 0 [3, 3, 3] = 5 := by
  have four : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow]
    norm_num
  norm_num [Bounds.dynamicFingerCostFrom, Nat.dist, four]

-- The public consequence applies to the actual cost-annotated optimizer,
-- retaining its exact tree and its work certificate.
example (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t = (OptimalLazyFinger.Work.tree n xs).ret ∧ t.size = n ∧
      (OptimalLazyFinger.Work.tree n xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 ∧
      (LazyFinger.cost t xs : ℝ) ≤ 2 * Bounds.staticCost n xs ∧
      (∀ f, (LazyFinger.cost t xs : ℝ) ≤ 6 * Bounds.fingerCost f xs) ∧
      ∀ p, p < n → (LazyFinger.cost t xs : ℝ) ≤ n + 4 * Bounds.dynamicFingerCostFrom p xs := by
  obtain ⟨size, optimal, work⟩ := OptimalLazyFinger.Work.Results.root_start n xs valid
  refine ⟨_, rfl, size, work, ?_⟩
  rw [optimal]
  exact ⟨LazyFinger.Consequences.Results.static_optimality n xs valid,
    fun f => LazyFinger.Consequences.Results.static_finger n f xs valid,
    fun p hp => LazyFinger.Consequences.Results.dynamic_finger n p xs hp valid⟩

-- Empty universes and empty sequences are included in the entropy construction.
example : ∃ t : Tree, t.size = 0 ∧ (StaticTree.cost t [] : ℝ) ≤ 0 := by
  simpa [Bounds.staticCost] using StaticTree.Results.entropy_upper_bound 0 [] (by simp)

/-- info: 'RotationBST.LazyFinger.Consequences.Results.simultaneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LazyFinger.Consequences.Results.simultaneous

end RotationBST.Tests.LazyFingerConsequences
