module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Cut.Results.Abstract
public import RotationBST.Tango.State.Join.Results.Abstract

@[expose] public section
namespace RotationBST.Tango.State.Executable.Results
open MarkedTree Arboral.Region

/-- The auxiliary endpoint can be reconstructed by a concrete traversal,
retaining the entire marked fringe and exactly the given rotation count. -/
theorem reconstruction (s : MarkedTree) (target : Tree) (cost : Nat)
    (rotations : Rotations (shape s.region) target cost) :
    shape (rebuild target s.fringe).region = target ∧
      s.fringe = (rebuild target s.fringe).fringe ∧
      Rotations s.tree (rebuild target s.fringe).tree cost := rebuild_rotations s target cost rotations

/-- Executable component splaying has a whole-BST amortized bound. -/
theorem splay (s : MarkedTree) (rank : Nat) (valid : rank < s.region.size) :
    s.fringe = (s.splayRoot rank).1.fringe ∧
      Access (shape s.region) (shape (s.splayRoot rank).1.region) rank (s.splayRoot rank).2 ∧
      Rotations s.tree (s.splayRoot rank).1.tree (s.splayRoot rank).2 ∧
      ((s.splayRoot rank).2 : ℝ) + (s.splayRoot rank).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := splayRoot_spec s rank valid

end RotationBST.Tango.State.Executable.Results

#check_bst_abstract RotationBST.Tango.State.Executable.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Arboral.Treap.Regions.Abstract,
  RotationBST.Tango.Auxiliary.Definitions.Abstract, RotationBST.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Pointer.Traces, RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract, RotationBST.Splay.Potential.Abstract]
