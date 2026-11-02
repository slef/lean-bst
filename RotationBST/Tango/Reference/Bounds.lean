module

public import RotationBST.Tango.Reference.Abstract
public import RotationBST.Tango.Bounds
import Mathlib.Data.Nat.Init

@[expose] public section
namespace RotationBST.Tango

theorem balanced_size (n : Nat) : (balanced n).size = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [balanced, Tree.size]
    | succ n =>
      rw [balanced, Tree.size, ih ((n + 1) / 2) (by omega), ih (n / 2) (by omega)]
      omega

/-- Fewer than `2^h` keys fit in reference height at most `h`. -/
theorem balanced_height_of_lt_pow (n h : Nat) (bound : n < 2 ^ h) : height (balanced n) ≤ h := by
  induction h generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using bound
    subst n
    simp [balanced, height]
  | succ h ih =>
    cases n with
    | zero => simp [balanced, height]
    | succ n =>
      have power : 2 ^ (h + 1) = 2 ^ h * 2 := Nat.pow_succ ..
      have left := ih ((n + 1) / 2) (by rw [power] at bound; omega)
      have right := ih (n / 2) (by rw [power] at bound; omega)
      rw [balanced, height]
      omega

/-- A logarithmic reference height is available for every universe size. -/
theorem balanced_height (n : Nat) : height (balanced n) ≤ Nat.log2 n + 1 :=
  balanced_height_of_lt_pow n (Nat.log2 n + 1) Nat.lt_log2_self

end RotationBST.Tango
