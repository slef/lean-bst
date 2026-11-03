module

public import RotationBST.Bounds.Interleave.Wilber.Abstract
import Mathlib.Tactic.SplitIfs
public import RotationBST.Bounds.Interleave.Wilber.Defs

@[expose] public section
namespace RotationBST.Wilber

/-- Restrict an absolute history to an interval and translate it to local ranks. -/
def localRequests (lo high : Nat) (xs : List Nat) : List Nat :=
  (xs.filter fun x => lo ≤ x ∧ x < high).map (· - lo)

theorem local_regions (lo l r : Nat) (xs : List Nat) :
    regions l (l + 1 + r) (localRequests lo (lo + l + 1 + r) xs) =
      labels lo (lo + l) (lo + l + 1 + r) xs := by
  induction xs with
  | nil => simp [regions, localRequests, labels]
  | cons x xs ih =>
    by_cases h : lo ≤ x ∧ x < lo + l + 1 + r
    · have hlt : x - lo < l + 1 + r := by omega
      have hle : (x - lo ≤ l) = (x ≤ lo + l) := propext (by omega)
      simpa [regions, localRequests, labels, h, hlt, hle] using congrArg
        (List.cons (decide (x ≤ lo + l))) ih
    · simpa [regions, localRequests, labels, h] using ih

theorem local_left (lo l r : Nat) (xs : List Nat) :
    leftRequests l (localRequests lo (lo + l + 1 + r) xs) = localRequests lo (lo + l) xs := by
  induction xs with
  | nil => simp [ leftRequests, localRequests]
  | cons x xs ih =>
    by_cases h : lo ≤ x ∧ x < lo + l + 1 + r
    · by_cases hl : x - lo < l
      · have hh : lo ≤ x ∧ x < lo + l := by omega
        simpa [List.filter_cons, leftRequests, localRequests, h, hl, hh] using congrArg (List.cons (x - lo)) ih
      · have hh : ¬ (lo ≤ x ∧ x < lo + l) := by omega
        have hbad : ¬ x < lo + l := by omega
        simpa [List.filter_cons, leftRequests, localRequests, h, hl, hbad] using ih
    · have hh : ¬ (lo ≤ x ∧ x < lo + l) := by omega
      simpa [List.filter_cons, leftRequests, localRequests, h, hh] using ih

theorem local_right (lo l r : Nat) (xs : List Nat) :
    rightRequests l (localRequests lo (lo + l + 1 + r) xs) =
      localRequests (lo + l + 1) (lo + l + 1 + r) xs := by
  induction xs with
  | nil => simp [ rightRequests, localRequests]
  | cons x xs ih =>
    by_cases h : lo ≤ x ∧ x < lo + l + 1 + r
    · by_cases hr : l < x - lo
      · have hh : lo + l + 1 ≤ x ∧ x < lo + l + 1 + r := by omega
        have he : x - lo - l - 1 = x - (lo + l + 1) := by omega
        simpa [List.filter_cons, rightRequests, localRequests, h, hr, hh, he] using
          congrArg (List.cons (x - (lo + l + 1))) ih
      · have hh : ¬ (lo + l + 1 ≤ x ∧ x < lo + l + 1 + r) := by omega
        have hbad : ¬ lo + l + 1 ≤ x := by omega
        simpa [List.filter_cons, rightRequests, localRequests, h, hr, hbad] using ih
    · have hh : ¬ (lo + l + 1 ≤ x ∧ x < lo + l + 1 + r) := by omega
      simpa [List.filter_cons, rightRequests, localRequests, h, hh] using ih

private theorem absolute_eq_local (t : Tree) (lo : Nat) (xs : List Nat) :
    absoluteInterleave t lo xs = interleave t (localRequests lo (lo + t.size) xs) := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have he : lo + (l.size + 1 + r.size) = lo + l.size + 1 + r.size := by omega
    simp only [absoluteInterleave, interleave, Tree.size, he, local_regions, local_left,
      local_right, ← il, ← ir]

theorem absoluteInterleave_eq (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    absoluteInterleave t 0 xs = interleave t xs := by
  rw [absolute_eq_local]
  congr 1
  simp only [localRequests, Nat.zero_add, Nat.zero_le, true_and, Nat.sub_zero, List.map_id_fun']
  apply List.filter_eq_self.mpr
  intro x hx
  simpa using valid x hx

end RotationBST.Wilber
