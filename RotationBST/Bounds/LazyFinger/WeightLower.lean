module

public import RotationBST.Bounds.LazyFinger.Weights
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger
open WeightedFinger

private theorem root_lower (l r : Tree) (x y : Nat)
    (between : min x y ≤ l.size ∧ l.size ≤ max x y) :
    1 + (Tree.depth (.node l r) x : ℝ) + Tree.depth (.node l r) y ≤
      charge (StaticTree.weight (.node l r)) x y := by
  let t := Tree.node l r
  have massLower : (1 / 4 : ℝ) ≤ mass (StaticTree.weight t) x y := by
    rw [← StaticTree.weight_root l r]
    exact Finset.single_le_sum (fun k _ => (StaticTree.weight_pos t k).le) (Finset.mem_Icc.mpr between)
  have endpoint (z : Nat) (small : min (StaticTree.weight t x) (StaticTree.weight t y) ≤ StaticTree.weight t z) :
      2 * (Tree.depth t z : ℝ) ≤ Real.logb 2 (mass (StaticTree.weight t) x y /
        min (StaticTree.weight t x) (StaticTree.weight t y)) := by
    have positive := StaticTree.weight_pos t z
    have minimum : 0 < min (StaticTree.weight t x) (StaticTree.weight t y) :=
      lt_min (StaticTree.weight_pos t x) (StaticTree.weight_pos t y)
    have ratio : (1 / StaticTree.weight t z) / 4 ≤ mass (StaticTree.weight t) x y /
        min (StaticTree.weight t x) (StaticTree.weight t y) := by
      calc
        (1 / StaticTree.weight t z) / 4 = (1 / 4) / StaticTree.weight t z := by ring
        _ ≤ (1 / 4) / min (StaticTree.weight t x) (StaticTree.weight t y) :=
          div_le_div_of_nonneg_left (by norm_num) minimum small
        _ ≤ _ := div_le_div_of_nonneg_right massLower minimum.le
    have bound := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
    rw [Real.logb_div (by positivity) (by norm_num), StaticTree.log_weight] at bound
    have four : Real.logb 2 4 = 2 := by
      have h := Real.logb_pow 2 2 2
      norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
      exact h
    rw [four] at bound
    push_cast at bound
    linarith
  have left := endpoint x (min_le_left _ _)
  have right := endpoint y (min_le_right _ _)
  change 1 + (Tree.depth t x : ℝ) + Tree.depth t y ≤ 1 + _
  linarith

/-- The displayed inequality of Lemma 3 of arXiv:1304.6897: the same
geometrically decreasing tree weights also dominate movement distance.
The extra unit on both sides is the library's request normalization. -/
theorem distance_le_tree_charge (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    1 + (distance t x y : ℝ) ≤ charge (StaticTree.weight t) x y := by
  induction t generalizing x y with
  | nil => simp [Tree.size] at hx
  | node l r ihl ihr =>
    by_cases left : x < l.size ∧ y < l.size
    · rw [tree_charge_left l r x y left.1 left.2]
      simpa [distance, left] using ihl x y left.1 left.2
    · by_cases right : l.size < x ∧ l.size < y
      · have hxr : x - l.size - 1 < r.size := by simp only [Tree.size] at hx; omega
        have hyr : y - l.size - 1 < r.size := by simp only [Tree.size] at hy; omega
        have same := tree_charge_right l r (x - l.size - 1) (y - l.size - 1)
        have ex : l.size + 1 + (x - l.size - 1) = x := by omega
        have ey : l.size + 1 + (y - l.size - 1) = y := by omega
        rw [ex, ey] at same
        rw [same]
        simpa [distance, left, right] using ihr _ _ hxr hyr
      · have bound := root_lower l r x y (by omega)
        simpa [distance, left, right, Nat.cast_add, add_assoc] using bound

/-- Summing the pointwise inequality retains one unit per request. -/
theorem cost_le_tree_weighted (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    (costFrom t p xs : ℝ) ≤ WeightedFinger.costFrom (StaticTree.weight t) p xs := by
  induction xs generalizing p with
  | nil => simp [costFrom, WeightedFinger.costFrom]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have head := distance_le_tree_charge t p x hp hx
    have tail := ih x hx (fun y member => valid y (List.mem_cons_of_mem x member))
    simpa only [costFrom, WeightedFinger.costFrom, Nat.cast_add, Nat.cast_one] using add_le_add head tail

/-- One weighting works in both directions, uniformly over all valid pairs
and all request sequences on the given tree. -/
theorem exists_two_sided_weights (t : Tree) :
    ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
      (∀ x y, x < t.size → y < t.size →
        1 + (distance t x y : ℝ) ≤ WeightedFinger.charge w x y ∧
        WeightedFinger.charge w x y ≤ 3 + 2 * (distance t x y : ℝ)) ∧
      (∀ p xs, p < t.size → (∀ x ∈ xs, x < t.size) →
        (costFrom t p xs : ℝ) ≤ WeightedFinger.costFrom w p xs ∧
        WeightedFinger.costFrom w p xs ≤ 3 * (costFrom t p xs : ℝ)) :=
  ⟨StaticTree.weight t, StaticTree.weight_pos t,
    fun x y hx hy => ⟨distance_le_tree_charge t x y hx hy, tree_charge_le_distance t x y hx hy⟩,
    fun p xs hp valid => ⟨cost_le_tree_weighted t p xs hp valid, tree_weighted_cost_le t p xs hp valid⟩⟩

end RotationBST.LazyFinger
