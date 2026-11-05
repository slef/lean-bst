module

public import RotationBST.Bounds.ConditionalEntropy.Cycles
public import RotationBST.Bounds.Interleave.BitReversal.LowerBound

import Mathlib.Tactic

@[expose] public section
namespace RotationBST.ConditionalEntropy

/-- A repeated bit-reversal period has zero conditional information and a
logarithmic per-request lower bound against every conventional dynamic BST. -/
theorem bit_reversal_obstruction (h : Nat) :
    ∃ p < (Wilber.BitReversal.reference h).size, ∀ rounds,
      sequenceInformation (Wilber.BitReversal.reference h).size p
        (repeatPeriod (Wilber.BitReversal.requests h) rounds) = 0 ∧
      ∀ s t k, s.size = (Wilber.BitReversal.reference h).size →
        Pointer.Execution s (repeatPeriod (Wilber.BitReversal.requests h) rounds) t k →
        h * (repeatPeriod (Wilber.BitReversal.requests h) rounds).length ≤ 24 * k := by
  obtain ⟨p, member, zero⟩ := distinct_period_zero (Wilber.BitReversal.reference h).size
    (Wilber.BitReversal.requests h) (Wilber.BitReversal.requests_distinct h)
    (Wilber.BitReversal.requests_nonempty h)
  exact ⟨p, Wilber.BitReversal.requests_valid h p member, fun rounds =>
    ⟨zero rounds, fun _ _ _ size run => Wilber.BitReversal.repeated_pointer_lower h rounds size run⟩⟩

/-- No constant-factor conditional-entropy bound holds for conventional BSTs,
even after normalizing by one unit per request and allowing any one-time
universe-dependent startup cost. All dynamic initial shapes are covered. -/
theorem unbounded_with_startup (C : Nat) (allowance : Nat → Nat) :
    ∃ n p xs, 0 < n ∧ p < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      sequenceInformation n p xs = 0 ∧ adjacentInformation n xs = 0 ∧
      ∀ s t k, s.size = n → Pointer.Execution s xs t k → C * xs.length + allowance n < k := by
  let h := 24 * C + 24
  let n := (Wilber.BitReversal.reference h).size
  let rounds := 24 * allowance n + 2
  let xs := repeatPeriod (Wilber.BitReversal.requests h) rounds
  have positive : 0 < 2 ^ h := by positivity
  have universeSize := Wilber.BitReversal.reference_size h
  have length : xs.length = rounds * 2 ^ h := by
    simp only [xs, repeat_length, Wilber.BitReversal.requests_length]
  have nonempty : 0 < n := by dsimp [n]; rw [pow_succ] at universeSize; omega
  have long : n ≤ xs.length := by
    have hr : 2 ≤ rounds := by dsimp [rounds]; omega
    have scale := Nat.mul_le_mul_right (2 ^ h) hr
    rw [length]
    rw [pow_succ] at universeSize
    dsimp [n]
    nlinarith
  have gap : allowance n < xs.length := by
    have scale := Nat.mul_le_mul_left rounds positive
    rw [length]
    dsimp [rounds] at scale ⊢
    nlinarith
  obtain ⟨p, validP, obstruction⟩ := bit_reversal_obstruction h
  refine ⟨n, p, xs, nonempty, validP, long,
    repeat_valid n _ (Wilber.BitReversal.requests_valid h) rounds, (obstruction rounds).1,
    distinct_period_adjacent_zero n _ (Wilber.BitReversal.requests_distinct h) rounds, ?_⟩
  intro s t k size run
  have lower := (obstruction rounds).2 s t k size run
  change h * xs.length ≤ 24 * k at lower
  dsimp [h] at lower
  nlinarith

/-- The normalized conditional cost is exactly the request count on these
witnesses. This is stronger than merely observing zero unnormalized entropy. -/
theorem normalized_unbounded (C : Nat) (allowance : Nat → Nat) :
    ∃ n p xs, 0 < n ∧ p < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      entropy n p xs = 0 ∧ adjacentInformation n xs = 0 ∧ cost n p xs = (xs.length : ℝ) ∧
      ∀ s t k, s.size = n → Pointer.Execution s xs t k →
        (C : ℝ) * cost n p xs + allowance n < k := by
  obtain ⟨n, p, xs, hn, hp, long, valid, zero, adjacent, lower⟩ := unbounded_with_startup C allowance
  have normalized : cost n p xs = (xs.length : ℝ) := by simp [cost, zero]
  refine ⟨n, p, xs, hn, hp, long, valid, by simp [entropy, zero], adjacent, normalized, ?_⟩
  intro s t k size run
  rw [normalized]
  exact_mod_cast lower s t k size run

end RotationBST.ConditionalEntropy
