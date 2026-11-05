module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Separation.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Separation.Results

/-- The witnesses enumerate all ordered pairs in long alternating blocks. -/
theorem length (n rounds : Nat) : (pairSequence n rounds).length = 2 * rounds * n * n :=
  pairSequence_length n rounds

theorem valid (n rounds : Nat) : ∀ x ∈ pairSequence n rounds, x < n :=
  pairSequence_valid n rounds

/-- Uniform lower bound for every fixed lazy-finger reference tree. -/
theorem lazy_lower (t : Tree) (rounds r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    rounds * (r + 1) * t.size * t.size ≤ 2 * cost t (pairSequence t.size rounds) :=
  pairSequence_lower t rounds r large

/-- A legal dynamic execution of the same sequence, paying explicitly to
reshape between blocks and retaining every key. -/
theorem dynamic_upper (s : Tree) (rounds : Nat) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequence s.size rounds) t k ∧
      k ≤ s.size * s.size * (16 * s.size + 6 * rounds) := pairSequence_dynamic s rounds

/-- Long blocks make the dynamic execution linear in the number of requests. -/
theorem dynamic_linear (s : Tree) (rounds : Nat) (long : 16 * s.size ≤ rounds) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequence s.size rounds) t k ∧
      k ≤ 7 * rounds * s.size * s.size := pairSequence_dynamic_long s rounds long

/-- Strict lazy-finger/dynamic separation (Theorem 6 of arXiv:1304.6897).
The quantifiers allow the static optimum to choose its tree after seeing the
sequence, and allow any prescribed dynamic initial tree. -/
theorem strict (C : Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧ C * k < optimalCost n xs :=
  lazy_dynamic_unbounded C

/-- The gap survives every universe-dependent one-time initialization allowance. -/
theorem with_startup (C : Nat) (allowance : Nat → Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
        C * k + allowance n < optimalCost n xs := lazy_dynamic_unbounded_with_startup C allowance

theorem prescribed_length (n m : Nat) : (pairSequenceAtLength n m).length = m :=
  pairSequenceAtLength_length n m

theorem prescribed_valid (n m : Nat) (positive : 0 < n) :
    ∀ x ∈ pairSequenceAtLength n m, x < n := pairSequenceAtLength_valid n m positive

/-- Padding preserves the all-pairs lower bound in every static tree. -/
theorem prescribed_lower (t : Tree) (m r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    (m / (2 * t.size * t.size)) * (r + 1) * t.size * t.size ≤
      2 * cost t (pairSequenceAtLength t.size m) := pairSequenceAtLength_lower t m r large

/-- Both the repeated-key padding and its physical preparation are charged. -/
theorem prescribed_dynamic (s : Tree) (m : Nat) (positive : 0 < s.size)
    (long : 16 * s.size ≤ m / (2 * s.size * s.size)) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequenceAtLength s.size m) t k ∧
      k ≤ 14 * (m / (2 * s.size * s.size)) * s.size * s.size :=
  pairSequenceAtLength_dynamic s m positive long

/-- The strict separation holds at every sufficiently large prescribed length,
uniformly over dynamic initial trees and beyond any universe-dependent startup. -/
theorem all_lengths (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
          C * k + allowance n < optimalCost n xs := lazy_dynamic_all_lengths C allowance

/-- One family, fixed before the factor and initial tree are chosen, witnesses
an unbounded lazy-finger/dynamic separation ratio as length grows. -/
theorem family (allowance : Nat → Nat) :
    ∃ sizes : Nat → Nat, ∃ requests : Nat → List Nat,
      (∀ m, 0 < sizes m ∧ (requests m).length = m ∧
        (∀ x ∈ requests m, x < sizes m)) ∧
      ∀ C, ∃ threshold, ∀ m, threshold ≤ m →
        ∀ s : Tree, s.size = sizes m → ∃ t k, Pointer.Execution s (requests m) t k ∧
          C * k + allowance (sizes m) < optimalCost (sizes m) (requests m) :=
  lazy_dynamic_family allowance

end RotationBST.LazyFinger.Separation.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Separation.Results`: 13 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Separation.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Separation.Definitions.Abstract]
