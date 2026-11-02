module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.AbstractBridge
public import RotationBST.Tango.Algorithm.Abstract
public import RotationBST.Tango.LowerBound.Abstract
public import RotationBST.Tango.Paths.Results.Abstract
public import RotationBST.Tango.Auxiliary.Abstract
public import RotationBST.Tango.State.Abstract
public import RotationBST.Tango.State.Executable.Abstract
public import RotationBST.Tango.State.Nesting.Results.Abstract
public import RotationBST.Tango.State.Context.Results.Abstract
public import RotationBST.Tango.State.Context.Lookup.Results.Abstract
public import RotationBST.Tango.State.ComponentPath.Results.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Results.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Algorithm.Results.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Path.Results.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Path.Algorithm.Results.Abstract
public import RotationBST.Tango.State.Nesting.Edits.Whole.Abstract
public import RotationBST.Tango.State.Preferences.Results.Abstract
public import RotationBST.Tango.Preferences.Updates.Results.Abstract
public import RotationBST.Tango.Paths.Geometry.Results.Abstract

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
  RotationBST.Model.Abstract, RotationBST.Tango.Definitions.Abstract,
  RotationBST.Tango.Preferences.Abstract]
