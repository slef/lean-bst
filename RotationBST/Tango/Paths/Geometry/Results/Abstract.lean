module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.Paths.Geometry.Intervals

@[expose] public section
namespace RotationBST.Tango.Paths.Results

/-- Every computed preferred path is a downward path in the reference tree. -/
theorem reference_path (reference : Tree) (past : List Nat) {path : List Nat}
    (member : path ∈ preferredPaths reference past) : ReferencePath reference 0 path :=
  decompose_referencePaths reference 0 past path member

/-- Cutting by reference depth selects an interval in auxiliary key order. -/
theorem suffix_interval (reference : Tree) (past : List Nat) {path : List Nat}
    (member : path ∈ preferredPaths reference past) (k : Nat) : KeyInterval (path.drop k) path :=
  referencePath_suffix_interval (reference_path reference past member) k

/-- The selected keys can be described by two boundary comparisons. -/
theorem suffix_boundaries (reference : Tree) (past : List Nat) {path : List Nat}
    (member : path ∈ preferredPaths reference past) (k : Nat) (nonempty : path.drop k ≠ []) :
    ∃ low high : Nat, low ≤ high ∧
      (path.drop k).toFinset = path.toFinset.filter (fun x => low ≤ x ∧ x ≤ high) :=
  preferred_suffix_window reference past member k nonempty

end RotationBST.Tango.Paths.Results

#check_bst_abstract RotationBST.Tango.Paths.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.Definitions.Abstract,
  RotationBST.Tango.Paths.Abstract, RotationBST.Tango.Paths.Geometry.Abstract,
  RotationBST.Tango.Wilber.Abstract, RotationBST.Tango.Transition.Abstract]
