module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Preferences.Updates.Counts
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open Wilber

theorem firstCharge_append (xs ys : List PreferenceUpdate) (w : Nat → ℝ) :
    firstCharge (xs ++ ys) w = firstCharge xs w + firstCharge ys w := by
  simp [firstCharge]

/-- The allowance counts each key once and does not depend on tree shape. -/
theorem allowance_eq_sum (t : Tree) (lo : Nat) (w : Nat → ℝ) :
    allowance t lo w = ((List.range' lo t.size).map w).sum := by
  induction t generalizing lo with
  | nil => simp [allowance, Tree.size]
  | node l r il ir =>
    simp only [allowance, il, ir, Tree.size]
    rw [← List.range'_append_1, ← List.range'_append_1]
    simp [List.map_append, List.sum_append, add_assoc, add_comm, add_left_comm]

private theorem root_charge (trace : List Bool) (next : Bool) (key : Nat) (w : Nat → ℝ) :
    (if trace ++ [next] = [] then 0 else w key) =
      (if trace = [] then 0 else w key) +
        firstCharge (if trace.getLast? = some next then [] else [⟨key, trace.getLast?, next⟩]) w := by
  cases trace with
  | nil => simp [firstCharge]
  | cons b bs =>
    have nonempty : (b :: bs).getLast? ≠ none := by simp
    cases last : (b :: bs).getLast? with
    | none => exact False.elim (nonempty last)
    | some old => by_cases same : old = next <;> simp [firstCharge, same]

/-- A request spends exactly the newly observed nodes' credit. This holds for
arbitrary weights, so no multiplicity is hidden by an unweighted bound. -/
theorem observed_step (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) (w : Nat → ℝ)
    (valid : x < t.size) :
    observedCharge t lo (past ++ [x]) w = observedCharge t lo past w +
      firstCharge (preferenceUpdates t lo past x) w := by
  induction t generalizing lo past x with
  | nil => simp [Tree.size] at valid
  | node l r il ir =>
    have hv : x < l.size + 1 + r.size := valid
    simp only [observedCharge, preferenceUpdates, ite_eq_left hv,
      regions_append, left_append, right_append, firstCharge_append]
    have region : regions l.size (l.size + 1 + r.size) [x] = [decide (x ≤ l.size)] := by
      simp [regions, hv]
    rw [region, root_charge]
    by_cases hl : x < l.size
    · have hr : ¬ l.size < x := by omega
      simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
        hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil]
      have inductionBound := il lo (leftRequests l.size past) x hl
      simp only [leftRequests] at inductionBound
      linarith
    · by_cases he : x = l.size
      · subst x
        simp [leftRequests, rightRequests, firstCharge, add_assoc, add_comm, add_left_comm]
      · have hr : l.size < x := by omega
        have subvalid : x - l.size - 1 < r.size := by omega
        simp only [leftRequests, rightRequests, List.filter_cons, decide_eq_true_eq,
          hl, hr, ↓reduceIte, List.filter_nil, List.map_nil, List.append_nil,
          List.map_cons, ite_eq_right he]
        have inductionBound := ir (lo + l.size + 1) (rightRequests l.size past) (x - l.size - 1) subvalid
        simp only [rightRequests] at inductionBound
        linarith

/-- The actual first-setting log telescopes over arbitrary history prefixes. -/
theorem observed_log (t : Tree) (past xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) :
    observedCharge t 0 (past ++ xs) w = observedCharge t 0 past w +
      firstCharge (preferenceLog t past xs) w := by
  induction xs generalizing past with
  | nil => simp [preferenceLog, firstCharge]
  | cons x xs ih =>
    have first := observed_step t 0 past x w (valid x (by simp))
    have rest := ih (past ++ [x]) (fun y member => valid y (by simp [member]))
    simp only [preferenceLog, firstCharge_append]
    simpa only [List.append_assoc, List.singleton_append, first, add_assoc] using rest

theorem observed_empty (t : Tree) (lo : Nat) (w : Nat → ℝ) : observedCharge t lo [] w = 0 := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp [observedCharge, regions, leftRequests, rightRequests, il, ir]

theorem observed_le_allowance (t : Tree) (lo : Nat) (past : List Nat) (w : Nat → ℝ)
    (nonneg : ∀ key, lo ≤ key → key < lo + t.size → 0 ≤ w key) :
    observedCharge t lo past w ≤ allowance t lo w := by
  induction t generalizing lo past with
  | nil => exact le_rfl
  | node l r il ir =>
    have left := il lo (leftRequests l.size past) (by intro key lower upper; apply nonneg key lower; simp only [Tree.size]; omega)
    have right := ir (lo + l.size + 1) (rightRequests l.size past)
      (by intro key lower upper; apply nonneg key (by omega); simp only [Tree.size]; omega)
    have root := nonneg (lo + l.size) (by omega) (by simp only [Tree.size]; omega)
    simp only [observedCharge, allowance]
    split <;> linarith

/-- No prefix spends a node's initialization credit twice. After a nonempty
history, only the unspent credit is available to the suffix. -/
theorem remaining_budget (t : Tree) (past xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) (nonneg : ∀ key < t.size, 0 ≤ w key) :
    firstCharge (preferenceLog t past xs) w ≤ allowance t 0 w - observedCharge t 0 past w := by
  have exactCharge := observed_log t past xs w valid
  have bound := observed_le_allowance t 0 (past ++ xs) w (by simpa using nonneg)
  linarith

theorem first_budget (t : Tree) (xs : List Nat) (w : Nat → ℝ)
    (valid : ∀ x ∈ xs, x < t.size) (nonneg : ∀ key < t.size, 0 ≤ w key) :
    firstCharge (preferenceLog t [] xs) w ≤ allowance t 0 w := by
  simpa only [observed_empty, sub_zero] using remaining_budget t [] xs w valid nonneg

end RotationBST.Tango.Initialization
