module

public import RotationBST.Classical.WeightBalanced.Definitions.Abstract
public import RotationBST.Models.Rotation.Shapes
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

@[expose] public section

/-! A `β`-balanced tree has height at most `log_{1/β}(n + 1)`: weights shrink
by a factor `β` per level and never fall below one. The balanced tree is
`β`-balanced for every `β ≥ 2/3`. -/
namespace RotationBST.Classical.WeightBalanced
open _root_.RotationBST.Tree (height balanced)

theorem one_le_weight (t : Tree) : (1 : ℝ) ≤ weight t := by
  unfold weight; norm_cast; omega

theorem pow_height_le (β : ℝ) (hβ : 0 < β) (t : Tree) (h : Balanced β t) :
    (1 / β) ^ height t ≤ weight t := by
  induction t with
  | nil => simp [height, weight, Tree.size]
  | node l r il ir =>
    obtain ⟨hl, hr, bl, br⟩ := h
    have pl := il bl
    have pr := ir br
    simp only [height]
    rw [Nat.add_comm, pow_succ]
    have hb : 0 < 1 / β := by positivity
    rcases le_total (height l) (height r) with hlr | hlr
    · rw [max_eq_right hlr]
      calc (1 / β) ^ height r * (1 / β) ≤ (weight r : ℝ) * (1 / β) :=
            mul_le_mul_of_nonneg_right pr hb.le
        _ ≤ (β * weight (.node l r)) * (1 / β) := mul_le_mul_of_nonneg_right hr hb.le
        _ = weight (.node l r) := by field_simp
    · rw [max_eq_left hlr]
      calc (1 / β) ^ height l * (1 / β) ≤ (weight l : ℝ) * (1 / β) :=
            mul_le_mul_of_nonneg_right pl hb.le
        _ ≤ (β * weight (.node l r)) * (1 / β) := mul_le_mul_of_nonneg_right hl hb.le
        _ = weight (.node l r) := by field_simp

theorem height_le (β : ℝ) (hβ : 0 < β ∧ β < 1) (t : Tree) (h : Balanced β t) :
    (height t : ℝ) ≤ Real.logb (1 / β) (t.size + 1) := by
  have hp := pow_height_le β hβ.1 t h
  have hb : 1 < 1 / β := by rw [lt_div_iff₀ hβ.1]; linarith
  rw [Real.le_logb_iff_rpow_le hb (by positivity)]
  simpa [weight, Real.rpow_natCast] using hp

/-- The balanced tree is `β`-balanced for every `β ≥ 2/3` (two keys force `2/3`). -/
theorem balanced_balanced (β : ℝ) (hβ : 2 / 3 ≤ β) (n : Nat) : Balanced β (balanced n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [balanced, Balanced]
    | succ n =>
      rw [balanced]
      refine ⟨?_, ?_, ih _ (by omega), ih _ (by omega)⟩ <;>
      · simp only [weight, Tree.size, Tree.balanced_size]
        have h1 : (((n + 1) / 2 : Nat) : ℝ) * 3 + 1 ≤ 2 * (n + 1) := by
          have : (n + 1) / 2 * 3 + 1 ≤ 2 * (n + 1) := by omega
          exact_mod_cast this
        have h2 : ((n / 2 : Nat) : ℝ) ≤ ((n + 1) / 2 : Nat) := by exact_mod_cast Nat.div_le_div_right (by omega)
        have h3 : (((n + 1) / 2 + 1 + n / 2 + 1 : Nat) : ℝ) = n + 2 := by
          have : (n + 1) / 2 + 1 + n / 2 + 1 = n + 2 := by omega
          exact_mod_cast this
        push_cast at h3 ⊢
        nlinarith

end RotationBST.Classical.WeightBalanced
