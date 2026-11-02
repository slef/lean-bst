module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.Preferences.Updates.Comparison

@[expose] public section
namespace RotationBST.Tango.Updates.Results

/-- The log contains genuine changes, with no repeated node in one request. -/
theorem valid_log (t : Tree) (lo : Nat) (past : List Nat) (x : Nat) :
    ((preferenceUpdates t lo past x).map PreferenceUpdate.key).Nodup ∧
      ∀ e ∈ preferenceUpdates t lo past x,
        lo ≤ e.key ∧ e.key < lo + t.size ∧ e.previous ≠ some e.next := by
  refine ⟨preferenceUpdates_nodup t lo past x, ?_⟩
  intro e he
  have bounds := preferenceUpdates_bounds t lo past x e he
  exact ⟨bounds.1, bounds.2, preferenceUpdates_changed t lo past x e he⟩

theorem exact_count (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t [] xs).length = preferenceChanges t xs := by
  simpa only [List.nil_append, preferenceChanges_nil, Nat.zero_add] using
    (preferenceLog_count t [] xs valid).symm

/-- No future request changes any previously generated update. -/
theorem causal (t : Tree) (past xs ys : List Nat) :
    preferenceLog t past (xs ++ ys) = preferenceLog t past xs ++ preferenceLog t (past ++ xs) ys :=
  preferenceLog_append t past xs ys

/-- Initialization is charged at most once per reference node. -/
theorem interleave_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (preferenceLog t [] xs).length ≤ interleave t xs + t.size := preferenceLog_bound t xs valid

theorem offline_bound (reference : Tree) {s t : Tree} {xs : List Nat} {r : Nat}
    (size : reference.size = s.size) (execution : RotationBST.Execution s xs t r) :
    (preferenceLog reference [] xs).length ≤ 4 * r + 2 * xs.length + reference.size :=
  preferenceLog_le_rotations reference size execution

end RotationBST.Tango.Updates.Results

#check_bst_abstract RotationBST.Tango.Updates.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.Definitions.Abstract,
  RotationBST.Tango.Preferences.Abstract, RotationBST.Tango.Preferences.Updates.Abstract]
