module

public import RotationBST.Algorithms.Tango.State.Preferences.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Preference assignments at different reference keys commute exactly. -/
theorem setPreference_commute (s : MarkedTree) (x y : Nat) (a b : Bool)
    (different : x ≠ y) :
    (s.setPreference x a).setPreference y b = (s.setPreference y b).setPreference x a := by
  induction s generalizing x y with
  | nil => rfl
  | node l r cl cr il ir =>
    by_cases xl : x < l.tree.size <;> by_cases yl : y < l.tree.size <;>
      by_cases xr : x = l.tree.size <;> by_cases yr : y = l.tree.size
    all_goals try omega
    all_goals simp_all only [setPreference, setPreference_tree, ite_true, ite_false, Nat.lt_irrefl]
    all_goals first
      | rw [il x y different]
      | rw [ir (x - l.tree.size - 1) (y - l.tree.size - 1) (by omega)]

/-- Move an assignment through a log that never touches its key. -/
theorem setPreference_applyPreferences (s : MarkedTree) (key : Nat) (next : Bool)
    (updates : List PreferenceUpdate) (fresh : ∀ u ∈ updates, key ≠ u.key) :
    (s.setPreference key next).applyPreferences updates =
      (s.applyPreferences updates).setPreference key next := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih =>
    simp only [applyPreferences]
    rw [setPreference_commute s key u.key next u.next (fresh u (by simp))]
    exact ih _ (fun v member => fresh v (by simp [member]))

/-- Reversing distinct-key assignments changes no reference marks. This does
not equate the physical rotations or their costs in the two orders. -/
theorem applyPreferences_reverse (s : MarkedTree) (updates : List PreferenceUpdate)
    (distinct : updates.Pairwise (fun u v => u.key ≠ v.key)) :
    s.applyPreferences updates.reverse = s.applyPreferences updates := by
  induction updates generalizing s with
  | nil => rfl
  | cons u us ih =>
    obtain ⟨fresh, tail⟩ := List.pairwise_cons.mp distinct
    simp only [List.reverse_cons, applyPreferences_append, applyPreferences]
    rw [ih s tail]
    exact (setPreference_applyPreferences s u.key u.next us fresh).symm

end RotationBST.Tango.MarkedTree

namespace RotationBST.Tango
open Wilber

/-- A single request changes each reference node at most once. -/
theorem preferenceUpdates_distinct (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    (preferenceUpdates t lo past x).Pairwise (fun u v => u.key ≠ v.key) :=
  List.pairwise_map.mp (preferenceUpdates_nodup t lo past x)

end RotationBST.Tango

namespace RotationBST.Tango.MarkedTree

/-- Bottom-up updates realize exactly the same canonical next history. -/
theorem preferenceUpdates_reverse_canonical (t : Tree) (past : List Nat) (x : Nat)
    (history : ∀ y ∈ past, y < t.size) (valid : x < t.size) :
    (canonical t 0 past).applyPreferences (preferenceUpdates t 0 past x).reverse =
      canonical t 0 (past ++ [x]) := by
  rw [applyPreferences_reverse _ _ (preferenceUpdates_distinct t 0 past x)]
  exact preferenceUpdates_canonical t past x history valid

end RotationBST.Tango.MarkedTree
