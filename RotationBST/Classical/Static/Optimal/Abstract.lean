module

import RotationBST.Audit.Check
public import RotationBST.Classical.Static.Optimal.AbstractBridge

@[expose] public section

/-! Optimal static search trees: the cubic recurrence of Gilbert–Moore and
Knuth, Yao's quadrangle-inequality lemma, and Knuth's `O(n²)` algorithm.
`Definitions/Abstract` gives the recurrence (`cost`), its largest optimal roots
(`root`), the tree they build, Knuth's tables, and the key-weight instance. -/
namespace RotationBST.Classical.Static.Optimal.Results

/-! ### Any interval weight -/

/-- The recurrence builds a tree on the keys of `[i, j)`… -/
theorem tree_size (W : Nat → Nat → Nat) (i j : Nat) : (tree W i j).size = j - i :=
  Optimal.tree_size W i j

/-- …whose cost is the value of the recurrence… -/
theorem tree_cost (W : Nat → Nat → Nat) (i j : Nat) : treeCost W (tree W i j) i = cost W i j :=
  Optimal.tree_cost W i j

/-- …and no tree on those keys costs less. -/
theorem cost_le_treeCost (W : Nat → Nat → Nat) (t : Tree) (i j : Nat) (h : t.size = j - i) :
    cost W i j ≤ treeCost W t i :=
  Optimal.cost_le_treeCost W t i j h

/-- **Yao.** The optimal cost inherits the quadrangle inequality from a
monotone interval weight. -/
theorem cost_quadrangle (W : Nat → Nat → Nat) (hQ : Quadrangle W) (hM : Monotone W) :
    Quadrangle (cost W) :=
  Optimal.cost_quadrangle hQ hM

/-- **Knuth's inequalities**, first half: `R(i, j) ≤ R(i, j + 1)`. -/
theorem root_le_root_right (W : Nat → Nat → Nat) (hQ : Quadrangle W) (hM : Monotone W)
    {i j : Nat} (h : i < j) : root W i j ≤ root W i (j + 1) :=
  Optimal.root_le_root_right hQ hM h

/-- **Knuth's inequalities**, second half: `R(i, j) ≤ R(i + 1, j)`. -/
theorem root_le_root_left (W : Nat → Nat → Nat) (hQ : Quadrangle W) (hM : Monotone W)
    {i j : Nat} (h : i + 1 < j) : root W i j ≤ root W (i + 1) j :=
  Optimal.root_le_root_left hQ hM h

/-- Knuth's algorithm computes the recurrence… -/
theorem knuth_cost (W : Nat → Nat → Nat) (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    (knuth W n).1 = cost W 0 n :=
  Optimal.knuth_cost hQ hM n

/-- …examining at most `2n²` candidate roots. -/
theorem knuth_steps (W : Nat → Nat → Nat) (hQ : Quadrangle W) (hM : Monotone W) (n : Nat) :
    (knuth W n).2 ≤ 2 * n ^ 2 :=
  Optimal.knuth_steps hQ hM n

/-! ### Key weights -/

theorem rangeWeight_quadrangle (w : List Nat) : Quadrangle (rangeWeight w) :=
  Static.rangeWeight_quadrangle w

theorem rangeWeight_monotone (w : List Nat) : Monotone (rangeWeight w) :=
  Static.rangeWeight_monotone w

/-- The subtree-weight cost is the weighted depth cost. -/
theorem weightedCost_eq_treeCost (w : List Nat) (t : Tree) :
    weightedCost w t = treeCost (rangeWeight w) t 0 :=
  Static.weightedCost_eq_treeCost w t

theorem optTree_size (w : List Nat) : (optTree w).size = w.length :=
  Static.optTree_size w

theorem optTree_cost (w : List Nat) : weightedCost w (optTree w) = optCost w :=
  Static.optTree_cost w

theorem optCost_le (w : List Nat) (t : Tree) (h : t.size = w.length) :
    optCost w ≤ weightedCost w t :=
  Static.optCost_le w t h

theorem knuth_optCost (w : List Nat) : (knuth (rangeWeight w) w.length).1 = optCost w :=
  Static.knuth_optCost w

theorem knuth_steps_le (w : List Nat) : (knuth (rangeWeight w) w.length).2 ≤ 2 * w.length ^ 2 :=
  Static.knuth_steps_le w

/-! ### Request sequences: the best static tree -/

/-- Searching a fixed tree from the root costs its weighted cost under the
request counts. -/
theorem staticCost_eq_weightedCost (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    StaticTree.cost t xs = weightedCost (counts t.size xs) t :=
  Static.staticCost_eq_weightedCost t xs valid

theorem optTree_static (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optTree (counts n xs)).size = n ∧
      StaticTree.cost (optTree (counts n xs)) xs = optCost (counts n xs) :=
  ⟨Static.optTree_counts_size n xs, Static.optTree_static n xs valid⟩

theorem optCost_le_static (n : Nat) (xs : List Nat) (t : Tree) (ht : t.size = n)
    (valid : ∀ x ∈ xs, x < n) : optCost (counts n xs) ≤ StaticTree.cost t xs :=
  Static.optCost_le_static n xs t ht valid

/-- The best static tree lies between a third of the entropy bound and the
entropy bound itself. -/
theorem optCost_entropy (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    Bounds.staticCost n xs ≤ 3 * (optCost (counts n xs) : ℝ) ∧
      (optCost (counts n xs) : ℝ) ≤ Bounds.staticCost n xs :=
  ⟨Static.entropy_le_optCost n xs valid, Static.optCost_le_entropy n xs valid⟩

theorem optCost_le_balanced (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    optCost (counts n xs) ≤ xs.length * (Nat.log2 n + 1) :=
  Static.optCost_le_balanced n xs valid

end RotationBST.Classical.Static.Optimal.Results

/-- info: abstract audit passed for `RotationBST.Classical.Static.Optimal.Results`: 21 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.Static.Optimal.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Classical.Static.Definitions.Abstract,
  RotationBST.Classical.Static.Optimal.Definitions.Abstract]
