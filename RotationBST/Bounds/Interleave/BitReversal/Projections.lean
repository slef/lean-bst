module

public import RotationBST.Bounds.Interleave.BitReversal.Sequence

import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Wilber.BitReversal

private def alternating : Nat → List Bool
  | 0 => []
  | k + 1 => true :: false :: alternating k

private theorem doubled_left (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    leftRequests n (xs.flatMap fun x => [x, x + n + 1]) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := valid x (by simp)
    have tail := ih (by intro y hy; exact valid y (by simp [hy]))
    simp only [List.flatMap_cons, leftRequests, List.filter_append] at tail ⊢
    simpa [hx, show ¬ x + n + 1 < n by omega] using congrArg (x :: ·) tail

private theorem doubled_right (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    rightRequests n (xs.flatMap fun x => [x, x + n + 1]) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := valid x (by simp)
    have tail := ih (by intro y hy; exact valid y (by simp [hy]))
    simp only [List.flatMap_cons, rightRequests, List.filter_append, List.map_append] at tail ⊢
    simpa [show ¬ n < x by omega, show n < x + n + 1 by omega,
      show x + n + 1 - n - 1 = x by omega] using congrArg (x :: ·) tail

private theorem doubled_regions (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    regions n (n + 1 + n) (xs.flatMap fun x => [x, x + n + 1]) = alternating xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := valid x (by simp)
    have tail := ih (by intro y hy; exact valid y (by simp [hy]))
    simp only [List.flatMap_cons, regions, List.filter_append, List.map_append] at tail ⊢
    simpa [show x < n + 1 + n by omega, show x + n + 1 < n + 1 + n by omega,
      show x ≤ n by omega, show ¬ x + n + 1 ≤ n by omega, alternating]
      using congrArg (true :: false :: ·) tail

private theorem alternating_switches (k : Nat) : alternations (alternating (k + 1)) = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 1 + (1 + alternations (alternating (k + 1))) = _
    rw [ih]
    omega

theorem left_requests (h : Nat) :
    leftRequests (reference h).size (requests (h + 1)) = requests h :=
  doubled_left _ _ (requests_valid h)

theorem right_requests (h : Nat) :
    rightRequests (reference h).size (requests (h + 1)) = requests h :=
  doubled_right _ _ (requests_valid h)

/-- Consecutive requests alternate between the two child regions at the root. -/
theorem root_switches (h : Nat) :
    alternations (regions (reference h).size ((reference h).size + 1 + (reference h).size)
      (requests (h + 1))) + 1 = 2 * 2 ^ h := by
  rw [requests, doubled_regions _ _ (requests_valid h), requests_length]
  have positive : 0 < 2 ^ h := by positivity
  obtain ⟨k, eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [eq, alternating_switches]
  omega

end RotationBST.Wilber.BitReversal
