module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Cut.Results
public import RotationBST.Algorithms.Tango.State.Join.Results

@[expose] public section
namespace RotationBST.Tango.State.Executable.Results
open MarkedTree Geometric.Region

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

/-- info: abstract audit passed for `RotationBST.Tango.State.Executable.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.Executable.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs, RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs, RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract, RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces, RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract, RotationBST.Algorithms.Splay.Potential.Abstract, RotationBST.Models.Region.Defs, RotationBST.Algorithms.Tango.State.Abstract]
