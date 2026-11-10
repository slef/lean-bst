module

public import RotationBST.Classical.Static.Optimal.Knuth
public import RotationBST.Bounds.StaticTree.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section

/-! Key weights: interval weights are additive, so they satisfy the
quadrangle inequality with equality; the subtree-weight cost is the weighted
depth cost; and request counts turn it into the static search cost. -/
namespace RotationBST.Classical.Static
open Optimal

theorem rangeWeight_add (w : List Nat) {i j k : Nat} (h1 : i ≤ j) (h2 : j ≤ k) :
    rangeWeight w i j + rangeWeight w j k = rangeWeight w i k :=
  Finset.sum_Ico_consecutive _ h1 h2

theorem rangeWeight_quadrangle (w : List Nat) : Quadrangle (rangeWeight w) := by
  intro i i' j j' h1 h2 h3
  rw [← rangeWeight_add w h1 h2, ← rangeWeight_add w h2 h3, ← rangeWeight_add w h1 (h2.trans h3),
    ← rangeWeight_add w h2 h3]
  omega

theorem rangeWeight_monotone (w : List Nat) : Optimal.Monotone (rangeWeight w) := by
  intro i i' j j' h1 h2 h3
  rw [← rangeWeight_add w h1 (h2.trans h3), ← rangeWeight_add w h2 h3]
  omega

theorem rangeWeight_eq_range (w : List Nat) (lo n : Nat) :
    rangeWeight w lo (lo + n) = ∑ x ∈ Finset.range n, w.getD (lo + x) 0 := by
  rw [rangeWeight, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- The weighted depth cost of a tree on the keys `lo, lo + 1, …`. -/
theorem weighted_eq_treeCost (w : List Nat) (t : Tree) (lo : Nat) :
    ∑ x ∈ Finset.range t.size, w.getD (lo + x) 0 * (t.depth x + 1) =
      treeCost (rangeWeight w) t lo := by
  induction t generalizing lo with
  | nil => simp [Tree.size, treeCost]
  | node l r ihl ihr =>
    have hl := ihl lo
    have hr := ihr (lo + l.size + 1)
    rw [treeCost, ← hl, ← hr, rangeWeight_eq_range]
    simp only [Tree.size]
    rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_succ]
    have hleft : ∀ x ∈ Finset.range l.size,
        w.getD (lo + x) 0 * ((Tree.node l r).depth x + 1) =
          w.getD (lo + x) 0 + w.getD (lo + x) 0 * (l.depth x + 1) := by
      intro x hx
      have hx' := Finset.mem_range.mp hx
      simp only [Tree.depth, hx', ↓reduceIte]
      ring
    have hright : ∀ y ∈ Finset.range r.size,
        w.getD (lo + (l.size + 1 + y)) 0 * ((Tree.node l r).depth (l.size + 1 + y) + 1) =
          w.getD (lo + l.size + 1 + y) 0 + w.getD (lo + l.size + 1 + y) 0 * (r.depth y + 1) := by
      intro y _
      have h₁ : ¬ l.size + 1 + y < l.size := by omega
      have h₂ : l.size + 1 + y ≠ l.size := by omega
      have e : l.size + 1 + y - l.size - 1 = y := by omega
      simp only [Tree.depth, h₁, h₂, ↓reduceIte, e]
      rw [show lo + (l.size + 1 + y) = lo + l.size + 1 + y by omega]
      ring
    have hmid : (Tree.node l r).depth l.size = 0 := by simp [Tree.depth]
    rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright, hmid,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have e2 : ∀ y, w.getD (lo + (l.size + 1 + y)) 0 = w.getD (lo + l.size + 1 + y) 0 := by
      intro y; rw [show lo + (l.size + 1 + y) = lo + l.size + 1 + y by omega]
    simp only [e2]
    ring

theorem weightedCost_eq_treeCost (w : List Nat) (t : Tree) :
    weightedCost w t = treeCost (rangeWeight w) t 0 := by
  simpa [weightedCost] using weighted_eq_treeCost w t 0

theorem optTree_size (w : List Nat) : (optTree w).size = w.length := by
  simp [optTree, tree_size]

theorem optTree_cost (w : List Nat) : weightedCost w (optTree w) = optCost w := by
  rw [weightedCost_eq_treeCost, optTree, optCost, tree_cost]

theorem optCost_le (w : List Nat) (t : Tree) (h : t.size = w.length) :
    optCost w ≤ weightedCost w t := by
  rw [weightedCost_eq_treeCost, optCost]
  exact cost_le_treeCost _ t 0 w.length (by omega)

theorem knuth_optCost (w : List Nat) : (knuth (rangeWeight w) w.length).1 = optCost w :=
  knuth_cost (rangeWeight_quadrangle w) (rangeWeight_monotone w) w.length

theorem knuth_steps_le (w : List Nat) : (knuth (rangeWeight w) w.length).2 ≤ 2 * w.length ^ 2 :=
  knuth_steps (rangeWeight_quadrangle w) (rangeWeight_monotone w) w.length

/-! ### Request counts -/

theorem counts_length (n : Nat) (xs : List Nat) : (counts n xs).length = n := by
  simp [counts]

theorem counts_getD (n : Nat) (xs : List Nat) {x : Nat} (hx : x < n) :
    (counts n xs).getD x 0 = xs.count x := by
  simp [counts, List.getD_eq_getElem?_getD, hx]

/-- Searching a fixed tree from its root costs its weighted cost under the
request counts. -/
theorem staticCost_eq_weightedCost (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    StaticTree.cost t xs = weightedCost (counts t.size xs) t := by
  rw [weightedCost, Finset.sum_congr rfl fun x hx => by
    rw [counts_getD t.size xs (Finset.mem_range.mp hx)]]
  induction xs with
  | nil => simp [StaticTree.cost]
  | cons y ys ih =>
    have hy := valid y (by simp)
    have hrest := ih fun x hx => valid x (by simp [hx])
    simp only [StaticTree.cost, List.map_cons, List.sum_cons] at hrest ⊢
    rw [hrest]
    simp only [List.count_cons, beq_iff_eq, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_range, hy, ↓reduceIte]
    ring

end RotationBST.Classical.Static
