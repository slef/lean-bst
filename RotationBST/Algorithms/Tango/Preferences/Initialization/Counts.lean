module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open Wilber

theorem observed_one (t : Tree) (lo : Nat) (past : List Nat) :
    observedCharge t lo past (fun _ => 1) = (initializations t past : ℝ) := by
  induction t generalizing lo past with
  | nil => simp [observedCharge, initializations]
  | node l r il ir =>
    simp only [observedCharge, initializations, il, ir, Nat.cast_add]
    split <;> simp

theorem allowance_one (t : Tree) (lo : Nat) : allowance t lo (fun _ => 1) = (t.size : ℝ) := by
  induction t generalizing lo with
  | nil => simp [allowance, Tree.size]
  | node l r il ir => simp [allowance, Tree.size, il, ir]; ring

theorem firstCharge_one (updates : List PreferenceUpdate) :
    firstCharge updates (fun _ => 1) = ((updates.filter fun e => e.previous.isNone).length : ℝ) := by
  simp [firstCharge]

/-- Exactly the newly initialized reference nodes produce first-setting log
entries, also when resuming after a nonempty history. -/
theorem first_count (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t past xs |>.filter fun e => e.previous.isNone).length + initializations t past =
      initializations t (past ++ xs) := by
  have exactCharge := observed_log t past xs (fun _ => 1) valid
  rw [observed_one, observed_one, firstCharge_one] at exactCharge
  exact_mod_cast (show ((preferenceLog t past xs |>.filter fun e => e.previous.isNone).length : ℝ) +
    initializations t past = initializations t (past ++ xs) by linarith)

private theorem partition (updates : List PreferenceUpdate) :
    updates.length = (updates.filter fun e => e.previous.isNone).length +
      (updates.filter fun e => e.previous.isSome).length := by
  induction updates with
  | nil => rfl
  | cons e es ih => cases old : e.previous <;> simp [old, ih] <;> omega

/-- Removing first settings from the executable log leaves exactly Wilber's
interleave increment. Initialization is not charged to the offline bound. -/
theorem switch_count (t : Tree) (past xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t past xs |>.filter fun e => e.previous.isSome).length + interleave t past =
      interleave t (past ++ xs) := by
  have all := preferenceLog_count t past xs valid
  have first := first_count t past xs valid
  have split := partition (preferenceLog t past xs)
  rw [preferenceChanges_eq, preferenceChanges_eq] at all
  omega

end RotationBST.Tango.Initialization
