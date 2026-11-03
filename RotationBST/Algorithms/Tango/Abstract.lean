module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.AbstractBridge
public import RotationBST.Algorithms.Tango.Algorithm.Abstract
public import RotationBST.Bounds.Interleave.Abstract
public import RotationBST.Algorithms.Tango.Paths.Results
public import RotationBST.Algorithms.Tango.Auxiliary.Abstract
public import RotationBST.Algorithms.Tango.State.Results
public import RotationBST.Algorithms.Tango.State.Executable.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Results
public import RotationBST.Algorithms.Tango.State.Context.Results
public import RotationBST.Algorithms.Tango.State.Context.Lookup.Results
public import RotationBST.Algorithms.Tango.State.ComponentPath.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Results
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Whole.Results
public import RotationBST.Algorithms.Tango.State.Preferences.Results
public import RotationBST.Algorithms.Tango.Preferences.Updates.Results
public import RotationBST.Algorithms.Tango.Paths.Geometry.Results

@[expose] public section

/-! Preferred-path ingredients and the online policy existence/competitive
theorems, with executable preference edits and request serving. -/
namespace RotationBST.Tango.Results

/-- The interleave quantity counts exactly the switches of preferred regions.
First observations initialize a region and are not switches. -/
theorem interleave_switches (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) : interleave t xs = changeCost t [] xs := by
  simpa only [List.nil_append, interleave_nil, Nat.zero_add] using changeCost_eq t [] xs valid

theorem interleave_increment (t : Tree) (past : List Nat) (x : Nat) (valid : x < t.size) :
    interleave t (past ++ [x]) = interleave t past + changes t past x :=
  interleave_step t past x valid

/-- Initial preference settings add at most one charge per reference key. -/
theorem preference_settings (t : Tree) (xs : List Nat) :
    preferenceChanges t xs ≤ interleave t xs + t.size := preferenceChanges_bound t xs

/-- An auxiliary tree representing a preferred path has at most `height t` keys. -/
theorem path_size {t : Tree} {path : List Bool} (downward : DownwardPath t path) :
    path.length + 1 ≤ height t := downward_length downward

theorem perfect_reference (h : Nat) :
    (perfect h).size = 2 ^ h - 1 ∧ height (perfect h) = h :=
  ⟨perfect_size h, perfect_height h⟩

end RotationBST.Tango.Results

#check_bst_abstract RotationBST.Tango.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Abstract]
