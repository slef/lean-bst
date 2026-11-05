module

public import RotationBST.Bounds.WeightedFinger.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedFinger

theorem mass_symm (w : Nat → ℝ) (x y : Nat) : mass w x y = mass w y x := by
  simp [mass, min_comm, max_comm]

theorem charge_symm (w : Nat → ℝ) (x y : Nat) : charge w x y = charge w y x := by
  simp [charge, mass_symm w x y, min_comm]

theorem charge_self (w : Nat → ℝ) (x : Nat) (hx : 0 < w x) : charge w x x = 1 := by
  simp [charge, mass, ne_of_gt hx]

/-- Equal unit weights recover the ordinary dynamic-finger charge. -/
theorem charge_unit (x y : Nat) :
    charge (fun _ => 1) x y = 1 + Real.logb 2 ((max x y - min x y + 1 : Nat) : ℝ) := by
  have h : min x y ≤ max x y := le_trans (min_le_left _ _) (le_max_left _ _)
  simp [charge, mass, Nat.card_Icc, show max x y + 1 - min x y =
    max x y - min x y + 1 by omega]

theorem charge_ge_one (w : Nat → ℝ) (x y : Nat)
    (hw : ∀ k ∈ Finset.Icc (min x y) (max x y), 0 < w k) :
    1 ≤ charge w x y := by
  have hx : x ∈ Finset.Icc (min x y) (max x y) :=
    Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : y ∈ Finset.Icc (min x y) (max x y) :=
    Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩
  have hp : 0 < min (w x) (w y) := lt_min (hw x hx) (hw y hy)
  have hs : w x ≤ mass w x y := by
    exact Finset.single_le_sum (fun k hk => le_of_lt (hw k hk)) hx
  have hratio : 1 ≤ mass w x y / min (w x) (w y) :=
    (le_div_iff₀ hp).mpr (by simpa using le_trans (min_le_left _ _) hs)
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio
  unfold charge
  linarith

/-- Scaling all weights has no effect on the bound. -/
theorem charge_scale (w : Nat → ℝ) (c : ℝ) (hc : 0 < c) (x y : Nat) :
    charge (fun k => c * w k) x y = charge w x y := by
  have hm : mass (fun k => c * w k) x y = c * mass w x y := by
    simp [mass, Finset.mul_sum]
  unfold charge
  rw [hm, ← mul_min_of_nonneg _ _ (le_of_lt hc), mul_div_mul_left _ _ (ne_of_gt hc)]

end RotationBST.WeightedFinger
