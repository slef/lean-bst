module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Simulation

@[expose] public section
namespace RotationBST.Tango.State.EditAlgorithm.Results
open MarkedTree

/-- The computed interval cut implements the reference nesting edit, despite
arbitrary differences in the auxiliary binary shape. -/
theorem cut (s reference : MarkedTree) (same : s.nesting = reference.nesting)
    (i j : Nat) (ordered : i < j) (valid : j ≤ reference.region.size)
    (proper : j - i < reference.region.size) :
    (s.cutInterval i j).1.nesting = reference.nesting.group i (j - i + 1) ∧
      Rotations s.tree (s.cutInterval i j).1.tree (s.cutInterval i j).2 ∧
      ((s.cutInterval i j).2 : ℝ) + (s.cutInterval i j).1.potential - s.potential ≤
        6 * Real.logb 2 reference.region.size + 2 :=
  cutInterval_simulates s reference same i j ordered valid proper

/-- The computed merge implements the reference fringe splice, including an
attached component whose actual auxiliary shape differs from the reference. -/
theorem merge (s reference child : MarkedTree) (same : s.nesting = reference.nesting)
    (i : Nat) (positive : 0 < reference.region.size) (valid : i ≤ reference.region.size)
    (attached : reference.fringe[i]? = some child) :
    (s.mergeAt i).1.nesting = reference.nesting.merge i ∧
      Rotations s.tree (s.mergeAt i).1.tree (s.mergeAt i).2 ∧
      ((s.mergeAt i).2 : ℝ) + (s.mergeAt i).1.potential - s.potential ≤
        8 * Real.logb 2 (reference.region.size + child.region.size : Nat) + 2 :=
  mergeAt_simulates s reference child same i positive valid attached

end RotationBST.Tango.State.EditAlgorithm.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.EditAlgorithm.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.EditAlgorithm.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs, RotationBST.Algorithms.Tango.State.Nesting.Edits.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs, RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs, RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
