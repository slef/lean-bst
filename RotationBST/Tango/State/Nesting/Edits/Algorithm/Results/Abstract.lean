module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Nesting.Edits.Simulation

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

#check_bst_abstract RotationBST.Tango.State.EditAlgorithm.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Nesting.Abstract, RotationBST.Tango.State.Nesting.Edits.Abstract,
  RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Tango.State.Join.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
