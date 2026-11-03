module

public import RotationBST.Bounds.StaticTree.Weights
public import RotationBST.Bounds.Implications.Proofs
public import RotationBST.Algorithms.Splay.Pointer

@[expose] public section

namespace RotationBST.StaticTree

theorem length_le_cost (t : Tree) (xs : List Nat) : xs.length ≤ cost t xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [cost, List.map_cons, List.sum_cons, List.length_cons] at *; omega

/-- Frequency entropy is a lower bound, up to a fixed factor, on the cost of
searching any fixed BST on the same keys. -/
theorem entropy_le_cost (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    Bounds.staticCost t.size xs ≤ 3 * (cost t xs : ℝ) := by
  have h := Bounds.entropy_le_weighted t.size xs valid (weight t) (weight_pos t) 1
    (by norm_num) (weight_sum t)
  rw [Bounds.sum_count_mul t.size xs (fun x => Real.logb 2 (1 / weight t x)) valid] at h
  have hs : (xs.map fun x => Real.logb 2 (1 / weight t x)).sum = 2 * (cost t xs : ℝ) := by
    clear h valid
    induction xs with
    | nil => simp [cost]
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, cost, Nat.cast_add, Nat.cast_one] at *
        rw [log_weight]
        simp only [Nat.cast_add, Nat.cast_one]
        linarith
  rw [hs] at h
  have hl : (xs.length : ℝ) ≤ cost t xs := by exact_mod_cast length_le_cost t xs
  unfold Bounds.staticCost
  linarith

theorem locate_depth (t : Tree) (x : Nat) : (Splay.locate t x).context.length = depth t x := by
  induction t generalizing x with
  | nil => rfl
  | node l r il ir =>
      simp only [Splay.locate, depth]
      split
      · simp only [List.length_append, List.length_singleton, il]
      · split
        · rfl
        · simp only [List.length_append, List.length_singleton, ir]

/-- The fixed-tree search cost is realized exactly by downward pointer moves. -/
theorem serves (t : Tree) (x : Nat) (valid : x < t.size) :
    Pointer.Serves t t x (depth t x + 1) := by
  have ht := Splay.locate_trace t x valid
  rw [locate_depth] at ht
  have hc := Splay.locate_correct t x valid
  exact ⟨Splay.locate t x, Splay.locate t x, depth t x, 0,
    ht, hc.2.1, .refl, hc.1, by omega⟩

theorem execution (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    Pointer.Execution t xs t (cost t xs) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
      exact .cons (serves t x (valid x (by simp)))
        (ih (by intro y hy; exact valid y (by simp [hy])))

end RotationBST.StaticTree

namespace RotationBST

/-- Entropy-form static optimality implies comparison with every fixed BST,
with constants independent of both the initial and comparison shapes. -/
theorem HasStaticOptimalityBound.fixedTree (a : Algorithm) (h : HasStaticOptimalityBound a) :
    ∃ C D : Nat, ∀ t u xs, t.size = u.size → (∀ x ∈ xs, x < t.size) →
      (a.totalCost t xs : ℝ) ≤ (C : ℝ) * StaticTree.cost u xs +
        (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ)) := by
  obtain ⟨C, D, hc⟩ := h
  refine ⟨3 * C, D, ?_⟩
  intro t u xs same valid
  have hb := hc t xs valid
  have hv : ∀ x ∈ xs, x < u.size := by rwa [← same]
  have hs := StaticTree.entropy_le_cost u xs hv
  rw [← same] at hs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) C)
  push_cast
  nlinarith

end RotationBST
