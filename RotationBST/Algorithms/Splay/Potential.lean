module

public import RotationBST.Algorithms.Splay.Potential.Abstract
public import RotationBST.Algorithms.Splay.Online.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! The standard sum-of-log-subtree-masses potential on unlabelled shapes.
The only key identities are offsets in the implicit inorder numbering. -/
namespace RotationBST.Splay

variable {s t : Tree} {k : Nat}
open Pointer

theorem mass_nonneg (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (t : Tree) (lo : Nat) :
    0 ≤ mass w t lo := by
  induction t generalizing lo with
  | nil => exact le_rfl
  | node l r il ir =>
      dsimp only [mass]
      have := il lo
      have := ir (lo + l.size + 1)
      have := hw (lo + l.size)
      positivity

theorem mass_pos (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (l r : Tree) (lo : Nat) :
    0 < mass w (.node l r) lo := by
  have := mass_nonneg w hw l lo
  have := mass_nonneg w hw r (lo + l.size + 1)
  have := hw (lo + l.size)
  dsimp only [mass]
  positivity

theorem mass_rotate (w : Nat → ℝ) (h : Rotate s t) (lo : Nat) :
    mass w s lo = mass w t lo := by
  induction h generalizing lo with
  | right => simp only [mass, Tree.size, Nat.add_assoc]; ring
  | left => simp only [mass, Tree.size, Nat.add_assoc]; ring
  | inLeft h ih => simp only [mass, h.size_eq, ih]
  | inRight _ ih => simp only [mass, ih]

theorem mass_rotations (w : Nat → ℝ) (h : Rotations s t k) (lo : Nat) :
    mass w s lo = mass w t lo := by
  induction h with
  | refl => rfl
  | step h _ ih => exact (mass_rotate w h lo).trans ih

theorem mass_left_le (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (l r : Tree) (lo : Nat) :
    mass w l lo ≤ mass w (.node l r) lo := by
  have := mass_nonneg w hw r (lo + l.size + 1)
  have := hw (lo + l.size)
  simp only [mass]
  linarith

theorem mass_right_le (w : Nat → ℝ) (hw : ∀ i, 0 < w i) (l r : Tree) (lo : Nat) :
    mass w r (lo + l.size + 1) ≤ mass w (.node l r) lo := by
  have := mass_nonneg w hw l lo
  have := hw (lo + l.size)
  simp only [mass]
  linarith

end RotationBST.Splay
