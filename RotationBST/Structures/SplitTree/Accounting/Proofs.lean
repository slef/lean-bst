module

public import RotationBST.Structures.SplitTree.Accounting.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split

/-- The logarithmic reserve pays for the smaller-side term at a split. -/
theorem charge_reserve (left right : Nat) :
    charge left right + Nat.log2 (left + right + 2) ≤
      2 + Nat.log2 (left + 1) + Nat.log2 (right + 1) := by
  have bound (a b : Nat) (ordered : a ≤ b) :
      Nat.log2 (a + b + 2) ≤ Nat.log2 (b + 1) + 1 := by
    simp only [Nat.log2_eq_log_two]
    have h := Nat.log_mono_right (b := 2) (show a + b + 2 ≤ (b + 1) * 2 by omega)
    rwa [Nat.log_mul_base (by decide) (by omega)] at h
  rcases le_total left right with h | h
  · have := bound left right h
    simp only [charge, min_eq_left h]
    omega
  · have := bound right left h
    simp only [charge, min_eq_right h]
    have equal : right + left + 2 = left + right + 2 := by omega
    rw [equal] at this
    omega

/-- A complete split hierarchy costs at most twice its number of keys, with a
logarithmic reserve left over. No balance or split-order hypothesis is needed. -/
theorem totalCharge_reserve (t : Tree) :
    totalCharge t + Nat.log2 (t.size + 1) ≤ 2 * t.size := by
  induction t with
  | nil => decide
  | node l r il ir =>
    have step := charge_reserve l.size r.size
    simp only [totalCharge, Tree.size]
    have equal : l.size + 1 + r.size + 1 = l.size + r.size + 2 := by omega
    rw [equal]
    omega

theorem totalCharge_linear (t : Tree) : totalCharge t ≤ 2 * t.size := by
  have := totalCharge_reserve t
  omega

end RotationBST.Arboral.Split
