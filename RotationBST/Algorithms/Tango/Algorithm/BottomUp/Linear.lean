module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Startup
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.BottomUp
open MarkedTree Context Initialization Wilber

/-- First-join charges over an arbitrary continued history are paid by the
newly observed nodes' credit and one ancestor-attachment allowance per request. -/
theorem first_log_bound (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    firstLogCharge (canonical reference 0 past) (log reference past xs) ≤
      firstCharge (log reference past xs) (localCredit reference) +
        xs.length * (14 * Real.logb 2 (height reference) + 4) := by
  induction xs generalizing past with
  | nil => simp [log, firstLogCharge, firstCharge]
  | cons x xs ih =>
    have key := valid x (by simp)
    have extended : ∀ y ∈ past ++ [x], y < reference.size := by
      intro y member
      rcases List.mem_append.mp member with member | member
      · exact history y member
      · simpa only [List.mem_singleton.mp member] using key
    have first := request_first_charge reference past [] x history
      (by simpa only [plug, localCanonical_eq reference past history] using canonical_pathMarked reference 0 past) key
    simp only [plug, offset, localCanonical_eq reference past history, canonical_tree] at first
    have rest := ih (past ++ [x]) extended (fun y member => valid y (by simp [member]))
    simp only [log, firstLogCharge_append, preferenceUpdates_reverse_canonical reference past x history key,
      firstCharge_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The entire execution uses the fixed reference allowance once. The
additional logarithmic term belongs to requests, not to the universe size. -/
theorem startup_bound (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    firstLogCharge (initial reference) (log reference [] xs) ≤
      localAllowance reference + xs.length * (14 * Real.logb 2 (height reference) + 4) := by
  have bound := first_log_bound reference [] xs (by simp) valid
  rw [canonical_initial, firstCharge_log] at bound
  have credit := first_budget reference xs (localCredit reference) valid (fun key _ => localCredit_nonneg reference key)
  have total := allowance_localCredit reference 0
  simp only [Nat.sub_zero] at total
  rw [total] at credit
  linarith

/-- Resumed balanced-reference runs retain only their unspent linear credit. -/
theorem balanced_startup_remaining (n : Nat) (past xs : List Nat)
    (history : ∀ y ∈ past, y < n) (valid : ∀ x ∈ xs, x < n) :
    firstLogCharge (canonical (balanced n) 0 past) (log (balanced n) past xs) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) +
        xs.length * (14 * Real.logb 2 (height (balanced n)) + 4) := by
  have bound := first_log_bound (balanced n) past xs
    (by simpa only [balanced_size] using history) (by simpa only [balanced_size] using valid)
  have credit := balanced_remainingCharge n past xs valid
  linarith

/-- Concrete complete-run cost with a linear reference allowance and no
unresolved first-join charge. -/
theorem linear_run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤ localAllowance reference +
      interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
        xs.length * (17 * Real.logb 2 (height reference) + 5) := by
  have run := separated_run_bound p steps xs valid
  have startup := startup_bound reference xs valid
  nlinarith

/-- Against every offline rotation execution, initialization is charged by the
reference's local allowance, independently of the competitive coefficient. -/
theorem linear_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = serve s reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ localAllowance reference +
      (70 * Real.logb 2 (height reference) + 20) * (offline + xs.length : Nat) := by
  have valid : ∀ x ∈ xs, x < reference.size := by rw [size]; exact AccessBridge.execution_valid execution
  have bound := separated_competitive p steps size execution
  have startup := startup_bound reference xs valid
  have positive := Bounds.logb_nat_nonneg (height reference)
  simp only [Nat.cast_add] at bound ⊢
  nlinarith [mul_nonneg positive (Nat.cast_nonneg offline : (0 : ℝ) ≤ offline)]

/-- The computed balanced-reference policy has O(n) startup plus a doubly
logarithmic factor against any offline execution on the same universe. -/
theorem balanced_competitive (n : Nat) (p : Policy (balanced n))
    (steps : ∀ past s x, p.step past s x = serve s (balanced n) past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : start.size = n) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ 42 * n +
      (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) := by
  have bound := linear_competitive p steps ((balanced_size n).trans size.symm) execution
  have startup := balanced_localAllowance n
  have logarithm := Splay.Updates.log_nat_mono (balanced_height n)
  have scaled := mul_le_mul_of_nonneg_right logarithm (Nat.cast_nonneg (offline + xs.length) (α := ℝ))
  simp only [Nat.cast_add, Nat.cast_one] at logarithm scaled
  simp only [Nat.cast_add] at bound ⊢
  nlinarith

/-- Select one executable policy before requests and every offline comparator;
its startup coefficient does not grow with the reference height. -/
theorem balanced_policy (n : Nat) :
    ∃ p : Policy (balanced n),
      (∀ past s x, p.step past s x = serve s (balanced n) past x) ∧
      ∀ (start finish : Tree) (xs : List Nat) (offline : Nat), start.size = n →
        RotationBST.Execution start xs finish offline →
          ((p.run xs).2 : ℝ) + xs.length ≤ 42 * n +
            (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) := by
  refine ⟨policy (balanced n), fun _ _ _ => rfl, ?_⟩
  intro start finish xs offline size execution
  exact balanced_competitive n (policy (balanced n)) (fun _ _ _ => rfl) size execution

end RotationBST.Tango.BottomUp
