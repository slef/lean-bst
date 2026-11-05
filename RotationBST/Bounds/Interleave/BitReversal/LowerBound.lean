module

public import RotationBST.Bounds.Interleave.BitReversal.Projections
public import RotationBST.Bounds.Interleave.Superadditive
public import RotationBST.Bounds.Interleave.Abstract
public import RotationBST.Bounds.ConditionalEntropy.Deterministic

import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Wilber.BitReversal

/-- Each recursive child sees the smaller bit-reversal order, while every
consecutive pair of root observations switches sides. -/
theorem interleave_recurrence (h : Nat) :
    interleave (reference (h + 1)) (requests (h + 1)) + 1 =
      2 * 2 ^ h + 2 * interleave (reference h) (requests h) := by
  have root := root_switches h
  simp only [reference, interleave, left_requests, right_requests]
  omega

/-- The bit-reversal requests force a logarithmic number of interleaves per
request. Leaf ranks inhabit a universe with fewer than twice as many keys. -/
theorem interleave_lower (h : Nat) :
    h * 2 ^ h ≤ 2 * interleave (reference h) (requests h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have recurrence := interleave_recurrence h
    have positive : 0 < 2 ^ h := by positivity
    rw [pow_succ]
    nlinarith

end RotationBST.Wilber.BitReversal
namespace RotationBST.Wilber

theorem interleave_repeat (t : Tree) (period : List Nat) (rounds : Nat) :
    rounds * interleave t period ≤ interleave t (ConditionalEntropy.repeatPeriod period rounds) := by
  induction rounds with
  | zero => simp [ConditionalEntropy.repeatPeriod, interleave_nil]
  | succ rounds ih =>
    have concatenate := interleave_superadditive t period (ConditionalEntropy.repeatPeriod period rounds)
    change _ ≤ interleave t (period ++ ConditionalEntropy.repeatPeriod period rounds)
    nlinarith

end RotationBST.Wilber
namespace RotationBST.Wilber.BitReversal

/-- Repetition preserves the hard lower bound, without resetting the dynamic
BST or charging any hypothetical initialization between periods. -/
theorem repeated_pointer_lower (h rounds : Nat) {s t : Tree} {k : Nat}
    (size : s.size = (reference h).size)
    (run : Pointer.Execution s (ConditionalEntropy.repeatPeriod (requests h) rounds) t k) :
    h * (ConditionalEntropy.repeatPeriod (requests h) rounds).length ≤ 24 * k := by
  have base := interleave_lower h
  have repeated := interleave_repeat (reference h) (requests h) rounds
  have machine := Wilber.Results.pointer_lower_bound (reference h) size.symm run
  have scale := Nat.mul_le_mul_left rounds base
  rw [ConditionalEntropy.repeat_length, requests_length]
  nlinarith

/-- The same hard sequence also lower-bounds the simplified rotation model. -/
theorem repeated_rotation_lower (h rounds : Nat) {s t : Tree} {k : Nat}
    (size : s.size = (reference h).size)
    (run : RotationBST.Execution s (ConditionalEntropy.repeatPeriod (requests h) rounds) t k) :
    h * (ConditionalEntropy.repeatPeriod (requests h) rounds).length ≤
      8 * k + 4 * (ConditionalEntropy.repeatPeriod (requests h) rounds).length := by
  have base := interleave_lower h
  have repeated := interleave_repeat (reference h) (requests h) rounds
  have machine := Wilber.Results.rotation_lower_bound (reference h) size.symm run
  have scale := Nat.mul_le_mul_left rounds base
  rw [ConditionalEntropy.repeat_length, requests_length] at machine ⊢
  nlinarith

end RotationBST.Wilber.BitReversal
