module

public import RotationBST.Structures.Treap.Random.Common
public import RotationBST.Bounds.LazyFinger.Ancestors
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Data.Nat.Dist
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

@[expose] public section

/-! Expected depth in a random treap with uniform priorities: key `a` is an
ancestor of `x` exactly when it has the least priority between them, which
happens with probability `1/(|a - x| + 1)`. -/
namespace RotationBST.Classical.Random
open Treap.Random

theorem harmonic_real (k : Nat) : ((harmonic k : ℚ) : ℝ) = ∑ i ∈ Finset.range k, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

/-- Depth counts the proper ancestors on the search path. -/
theorem depth_eq_sum (t : Tree) (x : Nat) (hx : x < t.size) :
    (t.depth x : ℝ) = (∑ a ∈ Finset.range t.size,
      (if a ∈ t.searchPath 0 x ∧ a ∈ t.searchPath 0 x then 1 else 0 : ℝ)) - 1 := by
  have hl := LazyFinger.searchPath_length t 0 x ⟨Nat.zero_le _, by omega⟩
  simp only [and_self, Nat.sub_zero] at hl ⊢
  rw [Finset.sum_boole]
  have hf : (Finset.range t.size).filter (· ∈ t.searchPath 0 x) = (t.searchPath 0 x).toFinset := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, and_iff_right_iff_imp]
    intro h
    have := Tree.searchPath_bounds t 0 x a h
    omega
  rw [hf, List.toFinset_card_of_nodup (Tree.searchPath_nodup t 0 x), hl]
  push_cast; ring

/-- The ancestor probabilities sum to `H(x + 1) + H(n - x) - 1`. -/
theorem sum_inv_dist (n x : Nat) (hx : x < n) :
    ∑ a ∈ Finset.range n, ((Nat.dist a x : ℝ) + 1)⁻¹ =
      ((harmonic (x + 1) : ℚ) : ℝ) + ((harmonic (n - x) : ℚ) : ℝ) - 1 := by
  rw [harmonic_real, harmonic_real]
  have hn : n = (x + 1) + (n - x - 1) := by omega
  conv_lhs => rw [hn]
  rw [Finset.sum_range_add]
  have hleft : ∑ a ∈ Finset.range (x + 1), ((Nat.dist a x : ℝ) + 1)⁻¹ =
      ∑ i ∈ Finset.range (x + 1), ((i : ℝ) + 1)⁻¹ := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.dist_eq_sub_of_le (by omega), show x - (x + 1 - 1 - i) = i by omega]
  have hright : ∑ j ∈ Finset.range (n - x - 1), ((Nat.dist (x + 1 + j) x : ℝ) + 1)⁻¹ =
      ∑ j ∈ Finset.range (n - x - 1), ((((j + 1 : Nat) : ℝ)) + 1)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.dist_eq_sub_of_le_right (by omega), show x + 1 + j - x = j + 1 by omega]
  rw [hleft, hright, show n - x = (n - x - 1) + 1 by omega,
    Finset.sum_range_succ' (fun i : Nat => ((i : ℝ) + 1)⁻¹) (n - x - 1)]
  push_cast
  ring

/-- **Expected depth in a random treap.** With uniformly random priorities, the
expected depth of key `x` among `n` keys is `H(x + 1) + H(n - x) - 2`. -/
theorem expected_depth (n x : Nat) (hx : x < n) (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) 0) :
    average (fun _ => 1) (Finset.range n) (fun xs => ((T xs).depth x : ℝ)) =
      ((harmonic (x + 1) : ℚ) : ℝ) + ((harmonic (n - x) : ℚ) : ℝ) - 2 := by
  have hpoint : (fun xs => ((T xs).depth x : ℝ)) = fun xs =>
      (∑ a ∈ Finset.range n,
        (if a ∈ (T xs).searchPath 0 x ∧ a ∈ (T xs).searchPath 0 x then 1 else 0 : ℝ)) - 1 := by
    funext xs
    have := depth_eq_sum (T xs) x (by rw [(spec xs).1]; exact hx)
    rwa [(spec xs).1] at this
  rw [hpoint, average_sub, average_sum, average_const _ _ _ (fun _ _ => one_pos)]
  have hterm : ∀ a ∈ Finset.range n,
      average (fun _ => 1) (Finset.range n)
        (fun xs => if a ∈ (T xs).searchPath 0 x ∧ a ∈ (T xs).searchPath 0 x then 1 else 0) =
      ((Nat.dist a x : ℝ) + 1)⁻¹ := by
    intro a ha
    have ha' := Finset.mem_range.mp ha
    have := common_ancestor_probability (fun _ => 1) n 0 (fun _ _ => one_pos) T
      (by simpa using spec) a x x ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩
      ⟨Nat.zero_le _, by omega⟩
    simp only [Nat.zero_add, ← Finset.range_eq_Ico, min_self, max_self, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, mul_one] at this
    rw [this, one_div]
    congr 1
    have e : max a x + 1 - min a x = Nat.dist a x + 1 := by
      rcases le_total a x with h | h
      · rw [min_eq_left h, max_eq_right h, Nat.dist_eq_sub_of_le h]; omega
      · rw [min_eq_right h, max_eq_left h, Nat.dist_eq_sub_of_le_right h]; omega
    rw [e, Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_congr rfl hterm, sum_inv_dist n x hx]
  ring

/-- `H(k) ≤ 1 + ln k`, from `ln y ≤ y - 1` at `y = i / (i + 1)`. -/
theorem harmonic_le_one_add_log (k : Nat) : ((harmonic k : ℚ) : ℝ) ≤ 1 + Real.log k := by
  rw [harmonic_real]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · have hk : (0 : ℝ) < k := by exact_mod_cast h
      have hstep : ((k : ℝ) + 1)⁻¹ ≤ Real.log ((k : ℝ) + 1) - Real.log k := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k / (k + 1) by positivity)
        rw [Real.log_div hk.ne' (by positivity)] at this
        have e : (k : ℝ) / (k + 1) - 1 = -((k : ℝ) + 1)⁻¹ := by field_simp; ring
        linarith
      push_cast
      linarith

/-- In particular the expected depth is at most `2 ln n`. -/
theorem expected_depth_le (n x : Nat) (hx : x < n) (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) 0) :
    average (fun _ => 1) (Finset.range n) (fun xs => ((T xs).depth x : ℝ)) ≤ 2 * Real.log n := by
  rw [expected_depth n x hx T spec]
  have h1 := harmonic_le_one_add_log (x + 1)
  have h2 := harmonic_le_one_add_log (n - x)
  have l1 : Real.log ((x + 1 : Nat) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hx)
  have l2 : Real.log ((n - x : Nat) : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast (show 0 < n - x by omega)) (by exact_mod_cast Nat.sub_le n x)
  linarith

end RotationBST.Classical.Random
