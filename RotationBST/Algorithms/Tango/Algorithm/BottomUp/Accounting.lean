module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Execution
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Separation
public import RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Initialization Wilber

/-- Appending requests retains all previous bottom-up updates as a prefix. -/
theorem log_append (reference : Tree) (past xs ys : List Nat) :
    log reference past (xs ++ ys) = log reference past xs ++ log reference (past ++ xs) ys := by
  induction xs generalizing past with
  | nil => simp [log]
  | cons x xs ih => simp [log, ih, List.append_assoc]

/-- Reordering within a request preserves the number of emitted changes. -/
theorem log_length (reference : Tree) (past xs : List Nat) :
    (log reference past xs).length = (preferenceLog reference past xs).length := by
  induction xs generalizing past with
  | nil => rfl
  | cons x xs ih => simp only [log, preferenceLog, List.length_append, List.length_reverse, ih]

theorem log_keys (reference : Tree) (past xs : List Nat) :
    ∀ u ∈ log reference past xs, u.key < reference.size := by
  induction xs generalizing past with
  | nil => simp [log]
  | cons x xs ih =>
    intro u member
    rcases List.mem_append.mp member with member | member
    · simpa only [Nat.zero_add] using
        (preferenceUpdates_bounds reference 0 past x u (List.mem_reverse.mp member)).2
    · exact ih (past ++ [x]) u member

/-- Every complete bottom-up log realizes the exact next history. -/
theorem log_canonical (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    (canonical reference 0 past).applyPreferences (log reference past xs) =
      canonical reference 0 (past ++ xs) := by
  induction xs generalizing past with
  | nil => simp [log, applyPreferences]
  | cons x xs ih =>
    have key := valid x (by simp)
    have extended : ∀ y ∈ past ++ [x], y < reference.size := by
      intro y member
      rcases List.mem_append.mp member with member | member
      · exact history y member
      · simpa only [List.mem_singleton.mp member] using key
    rw [log, applyPreferences_append, preferenceUpdates_reverse_canonical reference past x history key,
      ih (past ++ [x]) extended (fun y member => valid y (by simp [member]))]
    simp only [List.append_assoc, List.singleton_append]

/-- Arbitrary per-key first-setting credits are unchanged by the within-request
reordering. This concerns credit, not physical execution cost. -/
theorem firstCharge_log (reference : Tree) (past xs : List Nat) (w : Nat → ℝ) :
    firstCharge (log reference past xs) w = firstCharge (preferenceLog reference past xs) w := by
  induction xs generalizing past with
  | nil => rfl
  | cons x xs ih =>
    simp only [log, preferenceLog, firstCharge_append, ih]
    congr 1
    simp [firstCharge, List.filter_reverse, List.map_reverse]

/-- Local credit is still linear for the reordered executable log. -/
theorem balanced_remainingCharge (n : Nat) (past xs : List Nat)
    (valid : ∀ key ∈ xs, key < n) :
    firstCharge (log (balanced n) past xs) (localCredit (balanced n)) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) := by
  rw [firstCharge_log]
  exact Initialization.balanced_remainingCharge n past xs valid

/-- Classifying events from their actual intermediate marks agrees with the
number of newly observed reference nodes, even in bottom-up order. -/
theorem firstCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    firstCount (canonical t 0 past) (log t past xs) + initializations t past =
      initializations t (past ++ xs) := by
  have extended : ∀ x ∈ past ++ xs, x < t.size := by
    intro x member
    rcases List.mem_append.mp member with member | member
    · exact history x member
    · exact valid x member
  have first := virgin_canonical t past history
  have last := virgin_canonical t (past ++ xs) extended
  have count := virgin_log (canonical t 0 past) (log t past xs)
    (by simpa only [canonical_tree] using log_keys t past xs)
  rw [log_canonical t past xs history valid] at count
  omega

theorem laterCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    laterCount (canonical t 0 past) (log t past xs) + interleave t past =
      interleave t (past ++ xs) := by
  have all := preferenceLog_count t past xs valid
  have first := firstCount_generated t past xs history valid
  have split := counts_partition (canonical t 0 past) (log t past xs)
  rw [log_length] at split
  rw [preferenceChanges_eq, preferenceChanges_eq] at all
  omega

/-- The physical log's exact charge separates into initialization and actual
preference switches, with components evaluated in the reordered execution. -/
theorem generated_split (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    logCharge (initial reference) (log reference [] xs) =
      firstLogCharge (initial reference) (log reference [] xs) +
        interleave reference xs * (14 * Real.logb 2 (height reference) + 4) := by
  have count := laterCount_generated reference [] xs (by simp) valid
  simp only [canonical_initial, interleave_nil, Nat.add_zero, List.nil_append] at count
  have split := logCharge_split (initial reference) (log reference [] xs)
    (by simpa only [initial_tree] using log_keys reference [] xs)
  simpa only [count, initial_tree] using split

theorem separated_run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤ firstLogCharge (initial reference) (log reference [] xs) +
      interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  simpa only [generated_split reference xs valid] using run_bound p steps xs valid

/-- This policy retains the previous offline comparison while exposing the
first-join charge that still needs the sharper initialization analysis. -/
theorem separated_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ firstLogCharge (initial reference) (log reference [] xs) +
      (56 * Real.logb 2 (height reference) + 16) * (offline + xs.length : Nat) := by
  have valid : ∀ x ∈ xs, x < reference.size := by
    rw [size]
    exact AccessBridge.execution_valid execution
  have bound := separated_run_bound p steps xs valid
  have lower := Wilber.interleave_le_rotations reference size execution
  have lowerReal : (interleave reference xs : ℝ) ≤ 4 * offline + 2 * xs.length := by exact_mod_cast lower
  have positive := Bounds.logb_nat_nonneg (height reference)
  simp only [Nat.cast_add]
  nlinarith [mul_nonneg positive (Nat.cast_nonneg offline : (0 : ℝ) ≤ offline),
    mul_nonneg positive (Nat.cast_nonneg xs.length : (0 : ℝ) ≤ xs.length)]

end RotationBST.Tango.BottomUp
