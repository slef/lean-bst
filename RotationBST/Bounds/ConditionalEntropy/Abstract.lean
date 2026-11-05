module

import RotationBST.Audit.Check
public import RotationBST.Bounds.ConditionalEntropy.AbstractBridge

@[expose] public section
namespace RotationBST.ConditionalEntropy.Results

/-- Conditional information is nonnegative, including empty rows. -/
theorem nonnegative (n : Nat) (f : Nat → Nat → Nat) : 0 ≤ information n f := information_nonneg n f

theorem request_charge (n p : Nat) (xs : List Nat) : (xs.length : ℝ) ≤ cost n p xs :=
  length_le_cost n p xs

/-- The normalized benchmark is exactly `m(1+H)`, also when `m = 0`. -/
theorem normalization (n p : Nat) (xs : List Nat) :
    cost n p xs = (xs.length : ℝ) * (1 + entropy n p xs) :=
  cost_eq_length_mul_entropy n p xs

/-- A deterministic successor gives zero information, even with unequal counts. -/
theorem deterministic (n : Nat) (f : Nat → Nat → Nat) (next : Nat → Nat)
    (unique : ∀ a b, b ≠ next a → f a b = 0) : information n f = 0 :=
  information_deterministic n f next unique

/-- Every repeated distinct-key period has zero adjacent-request information.
No external predecessor is part of this convention. -/
theorem adjacent_cycle (n : Nat) (period : List Nat) (distinct : period.Nodup) (rounds : Nat) :
    adjacentInformation n (repeatPeriod period rounds) = 0 :=
  distinct_period_adjacent_zero n period distinct rounds

/-- With an explicit predecessor, one choice works for every repetition count. -/
theorem cycle (n : Nat) (period : List Nat) (distinct : period.Nodup) (nonempty : period ≠ []) :
    ∃ p ∈ period, ∀ rounds, sequenceInformation n p (repeatPeriod period rounds) = 0 :=
  distinct_period_zero n period distinct nonempty

/-- Quantitative bit-reversal obstruction: logarithmic cost per request remains
necessary despite zero empirical conditional information. -/
theorem bit_reversal (h : Nat) :
    ∃ p < (Wilber.BitReversal.reference h).size, ∀ rounds,
      sequenceInformation (Wilber.BitReversal.reference h).size p
        (repeatPeriod (Wilber.BitReversal.requests h) rounds) = 0 ∧
      ∀ s t k, s.size = (Wilber.BitReversal.reference h).size →
        Pointer.Execution s (repeatPeriod (Wilber.BitReversal.requests h) rounds) t k →
        h * (repeatPeriod (Wilber.BitReversal.requests h) rounds).length ≤ 24 * k :=
  bit_reversal_obstruction h

/-- Lemma 7 of arXiv:1304.6897, strengthened to normalized request cost and
arbitrary universe-dependent startup allowances. Every initial shape and every
legal dynamic execution are quantified, including offline executions. -/
theorem obstruction (C : Nat) (allowance : Nat → Nat) :
    ∃ n p xs, 0 < n ∧ p < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      entropy n p xs = 0 ∧ adjacentInformation n xs = 0 ∧ cost n p xs = (xs.length : ℝ) ∧
      ∀ s t k, s.size = n → Pointer.Execution s xs t k →
        (C : ℝ) * cost n p xs + allowance n < k := normalized_unbounded C allowance

/-- The sequence's empirical information is the sum of the actual transition
charges; no independent or stationary source assumption is required. -/
theorem transitions (n p : Nat) (xs : List Nat)
    (initial : p < n) (valid : ∀ x ∈ xs, x < n) :
    transitionSum (fun a b => Real.logb 2
      ((rowTotal n (LazyFinger.frequency p xs) a : ℝ) / LazyFinger.frequency p xs a b)) p xs =
      sequenceInformation n p xs := sequenceInformation_transitions n p xs initial valid

end RotationBST.ConditionalEntropy.Results

/-- info: abstract audit passed for `RotationBST.ConditionalEntropy.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.ConditionalEntropy.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract,
  RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract,
  RotationBST.Bounds.Interleave.BitReversal.Definitions.Abstract]
