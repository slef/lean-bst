module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.AbstractBridge
public import RotationBST.Algorithms.Tango.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Reference.Abstract
public import RotationBST.Algorithms.Tango.Preferences.Abstract
public import RotationBST.Algorithms.Tango.Paths.Abstract
public import RotationBST.Algorithms.Tango.Auxiliary.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Executable.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Abstract

@[expose] public section

/-! Tango overview (Demaine, Harmon, Iacono, and Pătraşcu, 2007). The
vocabulary is in `Definitions/Abstract`, reference trees in `Reference/`,
preference counting in `Preferences/`, preferred paths in `Paths/`, auxiliary
trees in `Auxiliary/`, the executable policy in `Algorithm/Executable/Abstract`,
and the competitive theorems in `Algorithm/Abstract`. Wilber's lower bound,
which the competitive proof compares against, is in `Bounds/Interleave`.
The internal marked-tree state machine lives under `State/`. -/
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
  RotationBST.Algorithms.Tango.Definitions.Abstract, RotationBST.Algorithms.Tango.Preferences.Abstract]
