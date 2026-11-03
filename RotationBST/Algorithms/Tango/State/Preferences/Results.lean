module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Preferences.Correctness

@[expose] public section
namespace RotationBST.Tango.State.Preferences.Results
open MarkedTree

/-- The generated update log produces exactly the specified history marking. -/
theorem log_correct (reference : Tree) (past xs : List Nat)
    (history : ∀ y ∈ past, y < reference.size) (valid : ∀ x ∈ xs, x < reference.size) :
    (canonical reference 0 past).applyPreferences (preferenceLog reference past xs) =
      canonical reference 0 (past ++ xs) := preferenceLog_canonical reference past xs history valid

/-- Reference preference updates preserve the tree and its path marking. -/
theorem reference_update (s : MarkedTree) (updates : List PreferenceUpdate) (paths : s.PathMarked) :
    (s.applyPreferences updates).tree = s.tree ∧ (s.applyPreferences updates).PathMarked :=
  ⟨applyPreferences_tree s updates, applyPreferences_pathMarked s updates paths⟩

/-- Every intermediate reference component is bounded by reference height. -/
theorem component_bound (s : MarkedTree) (paths : s.PathMarked) :
    s.region.size ≤ height s.tree := region_size_le_height s paths

/-- A concrete preference update can be realized in any matching auxiliary shape. -/
theorem one_update (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : key < reference.tree.size) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤ 14 * Real.logb 2 (height reference.tree) + 4 :=
  realize_preference s reference key next same paths valid

/-- A whole update log composes with telescoping whole-BST potential. This is the
preference-maintenance phase; request visits must still be interleaved with it. -/
theorem update_sequence (s reference : MarkedTree) (updates : List PreferenceUpdate)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : ∀ update ∈ updates, update.key < reference.tree.size) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (reference.applyPreferences updates).nesting ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤
        updates.length * (14 * Real.logb 2 (height reference.tree) + 4) :=
  realize_preferences s reference updates same paths valid

end RotationBST.Tango.State.Preferences.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.Preferences.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.Preferences.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Canonical.Defs, RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Algorithms.Tango.State.Preferences.Defs, RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Algorithms.Tango.State.Nesting.Defs, RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
