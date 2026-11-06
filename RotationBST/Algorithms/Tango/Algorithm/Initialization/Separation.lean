module

public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Marks
public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Comparison
public import RotationBST.Algorithms.Tango.Algorithm.Competitive
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Wilber

private theorem update_split (reference : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < reference.tree.size) :
    updateCharge reference key next = (if firstAt reference key then updateCharge reference key next else 0) +
      (if firstAt reference key then 0 else 1) * (14 * Real.logb 2 (height reference.tree) + 4) := by
  obtain ⟨fs, l, r, cl, cr, located, _, _⟩ := locateKey_spec reference key next valid
  cases cl <;> cases cr <;> simp [updateCharge, firstAt, located]

/-- Split the charged executable log using the marks seen at each operation.
Only the later updates pay the uniform switch coefficient. -/
theorem logCharge_split (reference : MarkedTree) (updates : List PreferenceUpdate)
    (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    logCharge reference updates = firstLogCharge reference updates +
      laterCount reference updates * (14 * Real.logb 2 (height reference.tree) + 4) := by
  induction updates generalizing reference with
  | nil => simp [logCharge, firstLogCharge, laterCount]
  | cons u us ih =>
    have first := update_split reference u.key u.next (valid u (by simp))
    have rest := ih (reference.setPreference u.key u.next)
      (by intro v member; simpa only [setPreference_tree] using valid v (by simp [member]))
    simp only [setPreference_tree] at rest
    simp only [logCharge, firstLogCharge, laterCount, Nat.cast_add, rest]
    by_cases initial : firstAt reference u.key = true
    · simp only [ite_eq_left initial] at first ⊢
      simp [add_assoc]
    · simp only [ite_eq_right initial] at first ⊢
      norm_num only [Nat.cast_one]
      linarith

theorem firstLogCharge_le (reference : MarkedTree) (updates : List PreferenceUpdate)
    (paths : reference.PathMarked) (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    firstLogCharge reference updates ≤ firstCount reference updates *
      (14 * Real.logb 2 (height reference.tree) + 4) := by
  induction updates generalizing reference with
  | nil => simp [firstLogCharge, firstCount]
  | cons u us ih =>
    have first := updateCharge_le reference u.key u.next paths (valid u (by simp))
    have rest := ih (reference.setPreference u.key u.next) (setPreference_pathMarked reference u.key u.next paths)
      (by intro v member; simpa only [setPreference_tree] using valid v (by simp [member]))
    simp only [setPreference_tree] at rest
    simp only [firstLogCharge, firstCount, Nat.cast_add]
    by_cases initial : firstAt reference u.key = true
    · simp only [ite_eq_left initial, Nat.cast_one]
      nlinarith
    · simpa only [ite_eq_right initial, Nat.cast_zero, zero_add] using rest

/-- The complete generated log consists of exactly its initialization charge
and the interleave charge. No standalone n-times-height allowance is added. -/
theorem generated_split (reference : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    logCharge (initial reference) (preferenceLog reference [] xs) =
      firstLogCharge (initial reference) (preferenceLog reference [] xs) +
        interleave reference xs * (14 * Real.logb 2 (height reference) + 4) := by
  have count := laterCount_generated reference [] xs (by simp) valid
  simp only [canonical_initial, interleave_nil, Nat.add_zero, List.nil_append] at count
  have split := logCharge_split (initial reference) (preferenceLog reference [] xs)
    (by simpa only [initial_tree] using log_keys reference [] xs)
  simpa only [count, initial_tree] using split

/-- The remaining initialization obligation is the explicit firstLogCharge
term; all subsequent update costs are charged to Wilber's interleave bound. -/
theorem separated_run_bound {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤ firstLogCharge (initial reference) (preferenceLog reference [] xs) +
      interleave reference xs * (14 * Real.logb 2 (height reference) + 4) +
      xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  simpa only [generated_split reference xs valid] using run_bound p steps xs valid

/-- Compare the same executable policy with any offline execution while
retaining the exact initialization charge as the only remaining allowance. -/
theorem separated_competitive {reference : Tree} (p : Policy reference)
    (steps : ∀ past s x, p.step past s x = s.serve reference past x)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : RotationBST.Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤ firstLogCharge (initial reference) (preferenceLog reference [] xs) +
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

end RotationBST.Tango.Initialization
