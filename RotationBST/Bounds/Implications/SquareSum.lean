module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! The partial sums of `1/k²` are bounded by two. These weights give the
static-finger and recency potentials a size-independent total mass. -/
namespace RotationBST.Bounds

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

end RotationBST.Bounds
