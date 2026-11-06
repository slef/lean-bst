module

public import RotationBST.Algorithms.Tango.Algorithm.Initialization.Definitions.Abstract
public import RotationBST.Algorithms.Tango.State.Preferences.Correctness
public import RotationBST.Algorithms.Tango.Preferences.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization
open MarkedTree Wilber

/-- Setting a preference consumes one virgin node exactly when both old
reference marks were present; no update can create a new virgin node. -/
theorem virgin_step (reference : MarkedTree) (key : Nat) (next : Bool)
    (valid : key < reference.tree.size) :
    virginCount (reference.setPreference key next) + (if firstAt reference key then 1 else 0) =
      virginCount reference := by
  induction reference generalizing key with
  | nil => simp [tree, Tree.size] at valid
  | node l r cl cr il ir =>
    by_cases left : key < l.tree.size
    · have child := il key left
      obtain ⟨fs, a, b, ca, cb, found, _, _⟩ := locateKey_spec l key next left
      simp only [setPreference, ite_eq_left left, virginCount, firstAt, locateKey, found, Option.map_some] at *
      omega
    · by_cases root : key = l.tree.size
      · subst key
        cases cl <;> cases cr <;> cases next <;> simp [setPreference, firstAt, locateKey, virginCount] <;> omega
      · have right : key - l.tree.size - 1 < r.tree.size := by simp only [tree, Tree.size] at valid; omega
        have child := ir _ right
        obtain ⟨fs, a, b, ca, cb, found, _, _⟩ := locateKey_spec r (key - l.tree.size - 1) next right
        simp only [setPreference, ite_eq_right left, ite_eq_right root, virginCount,
          firstAt, locateKey, found, Option.map_some] at *
        omega

theorem virgin_log (reference : MarkedTree) (updates : List PreferenceUpdate)
    (valid : ∀ u ∈ updates, u.key < reference.tree.size) :
    firstCount reference updates + virginCount (reference.applyPreferences updates) = virginCount reference := by
  induction updates generalizing reference with
  | nil => simp [firstCount, applyPreferences]
  | cons u us ih =>
    have first := virgin_step reference u.key u.next (valid u (by simp))
    have rest := ih (reference.setPreference u.key u.next)
      (by intro v member; simpa only [setPreference_tree] using valid v (by simp [member]))
    simp only [firstCount, applyPreferences]
    omega

theorem counts_partition (reference : MarkedTree) (updates : List PreferenceUpdate) :
    firstCount reference updates + laterCount reference updates = updates.length := by
  induction updates generalizing reference with
  | nil => rfl
  | cons u us ih =>
    have rest := ih (reference.setPreference u.key u.next)
    simp only [firstCount, laterCount, List.length_cons]
    split <;> omega

theorem virgin_localCanonical (t : Tree) (past : List Nat) :
    virginCount (localCanonical t past) + initializations t past = t.size := by
  induction t generalizing past with
  | nil => rfl
  | node l r il ir =>
    have left := il (leftRequests l.size past)
    have right := ir (rightRequests l.size past)
    simp only [localCanonical, initializations, Tree.size]
    cases last : (regions l.size (l.size + 1 + r.size) past).getLast? with
    | none =>
      have empty : regions l.size (l.size + 1 + r.size) past = [] := List.getLast?_eq_none_iff.mp last
      simp only [empty, ite_true, virginCount, Bool.and_self, Nat.zero_add]
      omega
    | some b =>
      have nonempty : regions l.size (l.size + 1 + r.size) past ≠ [] := by
        intro empty
        simp only [empty, List.getLast?_nil] at last
        contradiction
      cases b <;> simp only [virginCount, Bool.and_false, Bool.false_and, Bool.false_eq_true,
        ite_false, ite_eq_right nonempty] <;> omega

theorem virgin_canonical (t : Tree) (past : List Nat) (history : ∀ x ∈ past, x < t.size) :
    virginCount (canonical t 0 past) + initializations t past = t.size := by
  rw [← localCanonical_eq t past history]
  exact virgin_localCanonical t past

theorem log_keys (t : Tree) (past xs : List Nat) :
    ∀ u ∈ preferenceLog t past xs, u.key < t.size := by
  induction xs generalizing past with
  | nil => simp [preferenceLog]
  | cons x xs ih =>
    intro u member
    rcases List.mem_append.mp member with member | member
    · simpa only [Nat.zero_add] using (preferenceUpdates_bounds t 0 past x u member).2
    · exact ih (past ++ [x]) u member

/-- Counts derived from the changing marks agree with the initialization
increment for the generated log, without trusting its metadata. -/
theorem firstCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    firstCount (canonical t 0 past) (preferenceLog t past xs) + initializations t past =
      initializations t (past ++ xs) := by
  have extended : ∀ x ∈ past ++ xs, x < t.size := by
    intro x member
    rcases List.mem_append.mp member with member | member
    · exact history x member
    · exact valid x member
  have first := virgin_canonical t past history
  have last := virgin_canonical t (past ++ xs) extended
  have count := virgin_log (canonical t 0 past) (preferenceLog t past xs)
    (by simpa only [canonical_tree] using log_keys t past xs)
  rw [preferenceLog_canonical t past xs history valid] at count
  omega

/-- Every remaining generated update is a genuine interleave switch. -/
theorem laterCount_generated (t : Tree) (past xs : List Nat)
    (history : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    laterCount (canonical t 0 past) (preferenceLog t past xs) + interleave t past =
      interleave t (past ++ xs) := by
  have all := preferenceLog_count t past xs valid
  have first := firstCount_generated t past xs history valid
  have split := counts_partition (canonical t 0 past) (preferenceLog t past xs)
  rw [preferenceChanges_eq, preferenceChanges_eq] at all
  omega

end RotationBST.Tango.Initialization
