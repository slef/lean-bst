module

public import RotationBST.WorkingSet.Recency
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace RotationBST.Splay

/-- Total weight is a function of the inorder interval, not of the tree shape. -/
theorem mass_eq_sum (w : Nat → ℝ) (t : Tree) (lo : Nat) :
    mass w t lo = ((List.range' lo t.size).map w).sum := by
  induction t generalizing lo with
  | nil => simp [mass, Tree.size]
  | node l r il ir =>
      simp only [mass, il, ir, Tree.size]
      rw [show l.size + 1 + r.size = l.size + (r.size + 1) by omega,
        ← List.range'_append_1]
      simp [List.range', List.sum_append, add_assoc]

end RotationBST.Splay

namespace RotationBST.Recency

noncomputable def squareSum (n : Nat) : ℝ :=
  ((List.range n).map fun i : Nat => (((i : ℝ) + 1) ^ 2)⁻¹).sum

theorem inv_square_le_gap (n : Nat) :
    (((n : ℝ) + 1) ^ 2)⁻¹ ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
  have hg : 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) =
      2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    field_simp
    ring
  rw [hg, inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem squareSum_le (n : Nat) : squareSum n ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [squareSum]
  | succ n ih =>
      have h := inv_square_le_gap n
      simp only [squareSum, List.range_succ, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Nat.cast_add, Nat.cast_one] at ih ⊢
      convert add_le_add ih h using 1; ring

theorem squareSum_le_two (n : Nat) : squareSum n ≤ 2 := by
  have h := squareSum_le n
  have : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith

theorem sum_weight (order : List Nat) (hn : order.Nodup) :
    (order.map (weight order)).sum = squareSum order.length := by
  have h := congrArg (fun ns : List Nat =>
    (ns.map fun i : Nat => (((i : ℝ) + 1) ^ 2)⁻¹).sum) (map_idxOf order hn)
  unfold weight squareSum
  simpa only [List.map_map, Function.comp_def] using h

/-- Every recency permutation has exactly the same total weight. -/
theorem mass_weight (order : List Nat) (t : Tree) (hp : order.Perm (List.range t.size)) :
    Splay.mass (weight order) t 0 = squareSum t.size := by
  have hn := hp.nodup_iff.mpr List.nodup_range
  rw [Splay.mass_eq_sum, ← List.range_eq_range']
  rw [← (hp.map (weight order)).sum_eq, sum_weight order hn, hp.length_eq]
  simp

end RotationBST.Recency
