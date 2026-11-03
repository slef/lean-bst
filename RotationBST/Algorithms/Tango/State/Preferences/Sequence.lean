module

public import RotationBST.Algorithms.Tango.State.Preferences.Realization

@[expose] public section
namespace RotationBST.Tango.MarkedTree

@[simp] theorem applyPreferences_tree (s : MarkedTree) (updates : List PreferenceUpdate) :
    (s.applyPreferences updates).tree = s.tree := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih => simp only [applyPreferences, ih, setPreference_tree]

theorem applyPreferences_pathMarked (s : MarkedTree) (updates : List PreferenceUpdate)
    (paths : s.PathMarked) : (s.applyPreferences updates).PathMarked := by
  induction updates generalizing s with
  | nil => exact paths
  | cons u us ih => exact ih _ (setPreference_pathMarked s u.key u.next paths)

/-- The executable update log has the telescoping whole-tree potential bound. -/
theorem updatePreferences_spec (s reference : MarkedTree) (updates : List PreferenceUpdate)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : ∀ update ∈ updates, update.key < reference.tree.size) :
    (s.updatePreferences reference updates).1.nesting = (reference.applyPreferences updates).nesting ∧
      Rotations s.tree (s.updatePreferences reference updates).1.tree (s.updatePreferences reference updates).2 ∧
      ((s.updatePreferences reference updates).2 : ℝ) +
        (s.updatePreferences reference updates).1.potential - s.potential ≤
          updates.length * (14 * Real.logb 2 (height reference.tree) + 4) := by
  induction updates generalizing s reference with
  | nil => exact ⟨same, .refl, by simp [updatePreferences]⟩
  | cons u us ih =>
    obtain ⟨nested, first, ba⟩ := updatePreference_spec s reference u.key u.next same paths
      (valid u (List.mem_cons_self ..))
    obtain ⟨finalNesting, remaining, bb⟩ := ih (s.updatePreference reference u.key u.next).1
      (reference.setPreference u.key u.next) nested
      (setPreference_pathMarked reference u.key u.next paths)
      (by intro v hv; simpa only [setPreference_tree] using valid v (List.mem_cons_of_mem _ hv))
    refine ⟨finalNesting, first.append remaining, ?_⟩
    simp only [setPreference_tree] at bb
    simp only [updatePreferences, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Preference-change costs telescope against the actual whole-BST potential.
The resulting state realizes the updated reference nesting. -/
theorem realize_preferences (s reference : MarkedTree) (updates : List PreferenceUpdate)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : ∀ update ∈ updates, update.key < reference.tree.size) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (reference.applyPreferences updates).nesting ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤
        updates.length * (14 * Real.logb 2 (height reference.tree) + 4) := by
  exact ⟨(s.updatePreferences reference updates).1, (s.updatePreferences reference updates).2,
    updatePreferences_spec s reference updates same paths valid⟩

end RotationBST.Tango.MarkedTree
