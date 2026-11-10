module

public import RotationBST.Models.Rotation.Basic
import Mathlib.Tactic

@[expose] public section

/-! Size and height of the balanced tree, depth below height, and how a
rank's depth changes under rotations. -/
namespace RotationBST

namespace Tree

theorem balanced_size (n : Nat) : (balanced n).size = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [balanced, Tree.size]
    | succ n =>
      rw [balanced, Tree.size, ih ((n + 1) / 2) (by omega), ih (n / 2) (by omega)]
      omega

/-- Fewer than `2^h` keys fit in a balanced tree of height at most `h`. -/
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

/-- The balanced tree has height at most `⌊log₂ n⌋ + 1`. -/
theorem balanced_height (n : Nat) : height (balanced n) ≤ Nat.log2 n + 1 :=
  balanced_height_of_lt_pow n (Nat.log2 n + 1) Nat.lt_log2_self

/-- Every key lies strictly above the height. -/
theorem depth_lt_height (t : Tree) (x : Nat) (hx : x < t.size) : t.depth x < height t := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r il ir =>
    simp only [Tree.depth, height]
    split
    · have := il x (by assumption); omega
    · split
      · omega
      · have := ir (x - l.size - 1) (by simp [Tree.size] at hx; omega); omega

theorem depth_left {l r : Tree} {x : Nat} (h : x < l.size) :
    (Tree.node l r).depth x = l.depth x + 1 := by
  simp [Tree.depth, h]

theorem depth_root {l r : Tree} {x : Nat} (h : x = l.size) : (Tree.node l r).depth x = 0 := by
  subst h; simp [Tree.depth]

theorem depth_right {l r : Tree} {x : Nat} (h : l.size < x) :
    (Tree.node l r).depth x = r.depth (x - l.size - 1) + 1 := by
  simp [Tree.depth, show ¬ x < l.size by omega, show x ≠ l.size by omega]

end Tree

private theorem Rotate.depth_both {s t : Tree} (h : Rotate s t) (x : Nat) :
    t.depth x ≤ s.depth x + 1 ∧ s.depth x ≤ t.depth x + 1 := by
  induction h generalizing x with
  | @right a b c =>
    have index : x - (a.size + 1 + b.size) - 1 = x - a.size - 1 - b.size - 1 := by omega
    simp only [Tree.depth, Tree.size, index]
    split_ifs <;> omega
  | @left a b c =>
    have index : x - (a.size + 1 + b.size) - 1 = x - a.size - 1 - b.size - 1 := by omega
    simp only [Tree.depth, Tree.size, index]
    split_ifs <;> omega
  | @inLeft a b c h ih =>
    have bound := ih x
    have size := h.size_eq
    simp only [Tree.depth, ← size]
    split_ifs <;> omega
  | @inRight a b c _ ih =>
    have bound := ih (x - c.size - 1)
    simp only [Tree.depth]
    split_ifs <;> omega

/-- A rotation at any depth changes every rank's depth by at most one. -/
theorem Rotate.depth_le {s t : Tree} (h : Rotate s t) (x : Nat) : t.depth x ≤ s.depth x + 1 :=
  (h.depth_both x).1

theorem Rotate.depth_le_reverse {s t : Tree} (h : Rotate s t) (x : Nat) : s.depth x ≤ t.depth x + 1 :=
  (h.depth_both x).2

/-- Depth drift is bounded by the number of rotations, in both directions. -/
theorem Rotations.depth_le {s t : Tree} {k : Nat} (h : Rotations s t k) (x : Nat) :
    t.depth x ≤ s.depth x + k := by
  induction h with
  | refl => omega
  | step h _ ih => have := h.depth_le x; omega

theorem Rotations.depth_le_reverse {s t : Tree} {k : Nat} (h : Rotations s t k) (x : Nat) :
    s.depth x ≤ t.depth x + k := by
  induction h with
  | refl => omega
  | step h _ ih => have := h.depth_le_reverse x; omega

end RotationBST
