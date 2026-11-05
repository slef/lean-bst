module

public import RotationBST.Bounds.ConditionalEntropy.Abstract
public import RotationBST.Bounds.Interleave.BitReversal.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ConditionalEntropy
open RotationBST.ConditionalEntropy

-- A nondeterministic outgoing row has positive information: not every
-- transition matrix collapses to zero under the finite endpoint convention.
example : sequenceInformation 2 0 [0, 1] = 2 := by
  norm_num [sequenceInformation, information, rowTotal, LazyFinger.frequency,
    Finset.sum_range_succ, Real.logb_self_eq_one]
example : adjacentInformation 2 [0, 0, 1] = 2 := by
  norm_num [adjacentInformation, sequenceInformation, information, rowTotal,
    LazyFinger.frequency, Finset.sum_range_succ, Real.logb_self_eq_one]
example : cost 2 0 [0, 1] = 4 := by
  norm_num [cost, sequenceInformation, information, rowTotal, LazyFinger.frequency,
    Finset.sum_range_succ, Real.logb_self_eq_one]

-- Internal separators remain in the reference universe but need not be searched.
example : Wilber.BitReversal.requests 3 = [0, 8, 4, 12, 2, 10, 6, 14] := by decide
example : (Wilber.BitReversal.reference 3).size = 15 := by decide
example : Wilber.interleave (Wilber.BitReversal.reference 3) (Wilber.BitReversal.requests 3) = 17 := by decide
example : Wilber.interleave (Wilber.BitReversal.reference 2)
    (repeatPeriod (Wilber.BitReversal.requests 2) 2) = 13 := by decide

-- Repeated cycles include wraparound transitions, with no reset of a BST.
example (rounds : Nat) : adjacentInformation 7
    (repeatPeriod (Wilber.BitReversal.requests 2) rounds) = 0 :=
  Results.adjacent_cycle 7 _ (Wilber.BitReversal.Results.distinct 2) rounds
example : ∃ p ∈ [0, 4, 2, 6], ∀ rounds,
    sequenceInformation 7 p (repeatPeriod [0, 4, 2, 6] rounds) = 0 :=
  Results.cycle 7 [0, 4, 2, 6] (by decide) (by decide)

-- Empty and singleton periods are included and remain request-normalized.
example (rounds : Nat) : adjacentInformation 0 (repeatPeriod [] rounds) = 0 :=
  Results.adjacent_cycle 0 [] (by simp) rounds
example : cost 1 0 [0, 0, 0] = 3 := by
  norm_num [cost, sequenceInformation, information, rowTotal, LazyFinger.frequency,
    Finset.sum_range_succ]
example : entropy 0 0 [] = 0 := by
  simp [entropy, sequenceInformation, information]

-- The lower bound is against arbitrary initial shapes and final trees.
example (h rounds : Nat) (s t : Tree) (k : Nat)
    (same : s.size = (Wilber.BitReversal.reference h).size)
    (run : Pointer.Execution s (repeatPeriod (Wilber.BitReversal.requests h) rounds) t k) :
    h * (rounds * 2 ^ h) ≤ 24 * k := by
  simpa only [repeat_length, Wilber.BitReversal.Results.length] using
    Wilber.BitReversal.Results.pointer h rounds same run

-- A large one-time allowance cannot repair a uniform conditional-entropy bound.
example (C : Nat) :
    ∃ n p xs, 0 < n ∧ p < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      entropy n p xs = 0 ∧ adjacentInformation n xs = 0 ∧ cost n p xs = (xs.length : ℝ) ∧
      ∀ s t k, s.size = n → Pointer.Execution s xs t k →
        (C : ℝ) * cost n p xs + (n ^ 3 : Nat) < k :=
  Results.obstruction C (fun n => n ^ 3)

end RotationBST.Tests.ConditionalEntropy
