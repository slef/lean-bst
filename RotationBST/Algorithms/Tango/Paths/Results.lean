module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Paths.Update

@[expose] public section
namespace RotationBST.Tango.Results

theorem preferred_partition (reference : Tree) (past : List Nat) :
    (preferredPaths reference past).flatten.Perm (List.range reference.size) :=
  preferredPaths_partition reference past

theorem preferred_path_sizes (reference : Tree) (past : List Nat) :
    ∀ path ∈ preferredPaths reference past, path ≠ [] ∧ path.length ≤ height reference := by
  intro path hp
  exact ⟨preferredPaths_nonempty reference past path hp, preferredPaths_size reference past path hp⟩

theorem requested_root_path (reference : Tree) (past : List Nat) (x : Nat) (valid : x < reference.size) :
    x ∈ (decomposePaths reference 0 (past ++ [x])).1 :=
  request_on_root_path reference 0 past x (Nat.zero_le _) (by simpa using valid)

end RotationBST.Tango.Results

/-- info: abstract audit passed for `RotationBST.Tango.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract, RotationBST.Bounds.Interleave.Wilber.Defs, RotationBST.Bounds.Interleave.Transition.Defs]
