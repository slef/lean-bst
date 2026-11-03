module

public import RotationBST.Algorithms.Tango.Preferences.Abstract
public import RotationBST.Bounds.Interleave.Basic

@[expose] public section
namespace RotationBST.Tango
open Wilber

theorem runs_eq (trace : List Bool) :
    runs trace = alternations trace + if trace = [] then 0 else 1 := by
  cases trace <;> simp [runs, alternations, Nat.add_comm]

theorem initializations_le_size (t : Tree) (xs : List Nat) : initializations t xs ≤ t.size := by
  induction t generalizing xs with
  | nil => simp [initializations, Tree.size]
  | node l r il ir =>
    have hl := il (leftRequests l.size xs)
    have hr := ir (rightRequests l.size xs)
    simp only [initializations, Tree.size]
    split <;> omega

theorem preferenceChanges_eq (t : Tree) (xs : List Nat) :
    preferenceChanges t xs = interleave t xs + initializations t xs := by
  induction t generalizing xs with
  | nil => rfl
  | node l r il ir =>
    simp only [preferenceChanges, interleave, initializations, runs_eq, il, ir]
    omega

/-- The initialization term in Tango's analysis is additive in the universe
size, rather than paid again for every access. -/
theorem preferenceChanges_bound (t : Tree) (xs : List Nat) :
    preferenceChanges t xs ≤ interleave t xs + t.size := by
  rw [preferenceChanges_eq]
  exact Nat.add_le_add_left (initializations_le_size t xs) _

end RotationBST.Tango
