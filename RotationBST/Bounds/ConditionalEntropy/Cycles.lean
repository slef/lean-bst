module

public import RotationBST.Bounds.ConditionalEntropy.Deterministic

import Mathlib.Logic.Function.Basic

@[expose] public section
namespace RotationBST.ConditionalEntropy

private theorem exists_map (xs ys : List Nat) (distinct : xs.Nodup) (same : xs.length = ys.length) :
    ∃ next : Nat → Nat, xs.map next = ys := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := by simpa using same.symm
    subst ys
    exact ⟨id, rfl⟩
  | cons a xs ih =>
    cases ys with
    | nil => simp at same
    | cons b ys =>
      obtain ⟨next, mapped⟩ := ih ys (List.nodup_cons.mp distinct).2 (by simpa using same)
      refine ⟨Function.update next a b, ?_⟩
      simp only [List.map_cons, Function.update_self, List.cons.injEq, true_and]
      rw [← mapped]
      apply List.map_congr_left
      intro x hx
      exact Function.update_of_ne (by intro equal; subst x; exact (List.nodup_cons.mp distinct).1 hx) _ _

private theorem follows_of_map (next : Nat → Nat) (p last : Nat) (xs : List Nat)
    (mapped : (p :: xs).map next = xs ++ [last]) : Follows next p (xs ++ [last]) := by
  induction xs generalizing p with
  | nil => exact ⟨by simpa using mapped, trivial⟩
  | cons x xs ih =>
    have eq := List.cons.inj mapped
    exact ⟨eq.1, ih x eq.2⟩

/-- A period with distinct keys admits a deterministic cyclic successor rule.
The predecessor is its last key, including the boundary into the next period. -/
theorem cycle_follows (xs : List Nat) (p : Nat) (distinct : (xs ++ [p]).Nodup) :
    ∃ next : Nat → Nat, Follows next p (xs ++ [p]) := by
  have parts := List.nodup_append.mp distinct
  have source : (p :: xs).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, parts.1⟩
    intro member
    exact parts.2.2 p member p (by simp) rfl
  obtain ⟨next, mapped⟩ := exists_map (p :: xs) (xs ++ [p]) source (by simp)
  exact ⟨next, follows_of_map next p p xs mapped⟩

/-- Repeating a distinct-key period gives zero conditional information when
its last key is supplied as the initial predecessor. -/
theorem repeated_cycle_zero (n : Nat) (xs : List Nat) (p rounds : Nat)
    (distinct : (xs ++ [p]).Nodup) :
    sequenceInformation n p (repeatPeriod (xs ++ [p]) rounds) = 0 := by
  obtain ⟨next, follows⟩ := cycle_follows xs p distinct
  exact sequenceInformation_follows n p _ next
    (follows_repeat next p (xs ++ [p]) follows (by simp) rounds)

/-- The predecessor can be selected once for all repetitions of a nonempty
period. No assumption that the period visits every key is required. -/
theorem distinct_period_zero (n : Nat) (period : List Nat) (distinct : period.Nodup)
    (nonempty : period ≠ []) :
    ∃ p ∈ period, ∀ rounds, sequenceInformation n p (repeatPeriod period rounds) = 0 := by
  cases backward : period.reverse with
  | nil => exact False.elim (nonempty (List.reverse_eq_nil_iff.mp backward))
  | cons p xs =>
    have period_eq : period = xs.reverse ++ [p] := by
      have eq := congrArg List.reverse backward
      simpa only [List.reverse_reverse, List.reverse_cons] using eq
    subst period
    exact ⟨p, by simp, fun rounds => repeated_cycle_zero n xs.reverse p rounds distinct⟩

/-- The ordinary adjacent-request convention also gives zero information for
repetitions of a distinct-key period, without selecting an external predecessor. -/
theorem distinct_period_adjacent_zero (n : Nat) (period : List Nat) (distinct : period.Nodup)
    (rounds : Nat) : adjacentInformation n (repeatPeriod period rounds) = 0 := by
  cases backward : period.reverse with
  | nil =>
    have empty : period = [] := List.reverse_eq_nil_iff.mp backward
    subst period
    have repeated : repeatPeriod [] rounds = [] := by
      induction rounds with
      | zero => rfl
      | succ rounds ih => exact ih
    rw [repeated]
    rfl
  | cons p xs =>
    have period_eq : period = xs.reverse ++ [p] := by
      have eq := congrArg List.reverse backward
      simpa only [List.reverse_reverse, List.reverse_cons] using eq
    subst period
    obtain ⟨next, follows⟩ := cycle_follows xs.reverse p distinct
    exact adjacentInformation_follows n p _ next
      (follows_repeat next p (xs.reverse ++ [p]) follows (by simp) rounds)

end RotationBST.ConditionalEntropy
