module

public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import RotationBST.Bounds.WeightedEntropy

@[expose] public section

namespace RotationBST.StaticTree

/-- A prefix code with two bits per comparison/termination step. -/
noncomputable def weight (t : Tree) (x : Nat) : ℝ := ((4 : ℝ) ^ (depth t x + 1))⁻¹

theorem weight_pos (t : Tree) (x : Nat) : 0 < weight t x := by
  unfold weight
  positivity

theorem weight_left (l r : Tree) (x : Nat) (hx : x < l.size) :
    weight (.node l r) x = weight l x / 4 := by
  simp only [weight, depth, ite_eq_left hx, pow_succ, mul_inv_rev]
  ring

theorem weight_root (l r : Tree) : weight (.node l r) l.size = 1 / 4 := by
  simp [weight, depth]

theorem weight_right (l r : Tree) (x : Nat) :
    weight (.node l r) (l.size + 1 + x) = weight r x / 4 := by
  have hn : ¬ l.size + 1 + x < l.size := by omega
  have he : ¬ l.size + 1 + x = l.size := by omega
  have hs : l.size + 1 + x - l.size - 1 = x := by omega
  simp only [weight, depth, ite_eq_right hn, ite_eq_right he, hs, pow_succ, mul_inv_rev]
  ring

/-- The code weights have total mass at most one for every tree shape. -/
theorem weight_sum (t : Tree) : ∑ x ∈ Finset.range t.size, weight t x ≤ 1 := by
  induction t with
  | nil => simp [Tree.size]
  | node l r il ir =>
      have he : (∑ x ∈ Finset.range (Tree.node l r).size, weight (.node l r) x) =
          (∑ x ∈ Finset.range l.size, weight l x) / 4 + 1 / 4 +
          (∑ x ∈ Finset.range r.size, weight r x) / 4 := by
        rw [Tree.size, Finset.sum_range_add, Finset.sum_range_succ, weight_root]
        have hl : (∑ x ∈ Finset.range l.size, weight (.node l r) x) =
            (∑ x ∈ Finset.range l.size, weight l x) / 4 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl (fun x hx => weight_left l r x (Finset.mem_range.mp hx))
        rw [hl]
        congr 1
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun x _ => weight_right l r x)
      rw [he]
      linarith

theorem log_weight (t : Tree) (x : Nat) :
    Real.logb 2 (1 / weight t x) = 2 * (depth t x + 1 : Nat) := by
  have hfour : Real.logb 2 4 = 2 := by
    have h := Real.logb_pow 2 2 2
    norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h
    exact h
  simp only [weight, one_div, inv_inv, Real.logb_pow, hfour]
  ring

end RotationBST.StaticTree
