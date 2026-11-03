module

public import RotationBST.Algorithms.Splay.Scanning.Definitions.Abstract
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace RotationBST.Splay.Scanning.Marked

theorem alpha_antitone {a b : Nat} (h : a ≤ b) : alpha b ≤ alpha a := by
  unfold alpha
  split <;> split <;> omega

/-- The small correction term pays for pairs whose right-spine rank difference
is too small for the quadratic part to pay on its own. -/
theorem alpha_pair (a b : Nat) :
    alpha (a + b) + alpha (b + 1) + 3 ≤ alpha a + alpha b + a := by
  unfold alpha
  split <;> split <;> split <;> split <;> omega

theorem credit_mono {g h k : Nat} (hk : h ≤ k) : credit g h ≤ credit g k := by
  have ha := alpha_antitone (show g - k ≤ g - h by omega)
  have hm := Nat.mul_self_le_mul_self hk
  unfold credit
  omega

theorem credit_expose (g : Nat) (hg : 1 ≤ g) : credit g 1 ≤ credit g 0 + 7 := by
  unfold credit alpha
  split <;> split <;> omega

/-- A middle pair pays for its two splay rotations. The accumulated replacement
may have smaller rank than the worst case used by the potential calculation. -/
theorem pair_credit (h b c k : Nat) (hz : h ≤ b + 1) (hw : b ≤ c) (hk : k ≤ h + 1) :
    credit (c + 2) k + credit (c + 1) b + 4 ≤
      credit (b + 1) h + credit (c + 1) (b + 1) := by
  have hm := credit_mono (g := c + 2) hk
  have ha := alpha_pair (b + 1 - h) (c - b)
  have he : b + 1 - h + (c - b) = c + 1 - h := by omega
  have hf : c - b + 1 = c + 1 - b := by omega
  have hg : c + 2 - (h + 1) = c + 1 - h := by omega
  have hh : c + 1 - (b + 1) = c - b := by omega
  rw [he, hf] at ha
  unfold credit at hm ⊢
  rw [hg] at hm
  rw [hh]
  have hbh : b + 1 - h + h = b + 1 := by omega
  nlinarith

end RotationBST.Splay.Scanning.Marked
