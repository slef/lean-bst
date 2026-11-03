module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Auxiliary.Join

@[expose] public section
namespace RotationBST.Tango.Auxiliary.Results
open Geometric Region

/-- Two boundary splays detach an interior interval `[i,j)`. -/
theorem cut_interval (s : Region) (i j : Nat)
    (positive : 0 < i) (ordered : i ≤ j) (interior : j < s.size) :
    ∃ a middle c : Region, ∃ cost,
      a.size + 1 = i ∧ middle.size = j - i ∧
      a.size + middle.size + c.size + 2 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a (.node middle c)).fringe ∧
      Rotations s.tree (.node a.tree (.node middle.tree c.tree)) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.node (.hole middle.tree) c)) +
        auxiliaryPotential middle - auxiliaryPotential s ≤ 6 * Real.logb 2 s.size + 2 :=
  auxiliary_cut_interior s i j positive ordered interior

/-- Merge the component at an interior fringe position into its parent. -/
theorem join_interval (s middle : Region) (i : Nat) (positive : 0 < i) (interior : i < s.size)
    (attached : s.fringe[i]? = some middle.tree) :
    ∃ a c : Region, ∃ cost,
      a.size + 1 = i ∧ a.size + c.size + 2 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a (.node (.hole middle.tree) c)).fringe ∧
      Rotations s.tree (.node a.tree (.node middle.tree c.tree)) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.node middle c)) -
        auxiliaryPotential s - auxiliaryPotential middle ≤
          8 * Real.logb 2 (s.size + middle.size : Nat) + 2 :=
  auxiliary_join_interior s middle i positive interior attached

/-- The leftmost interval uses only its successor boundary. -/
theorem cut_prefix (s : Region) (j : Nat) (valid : j < s.size) :
    ∃ middle c : Region, ∃ cost,
      middle.size = j ∧ middle.size + c.size + 1 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node middle c).fringe ∧
      Rotations s.tree (.node middle.tree c.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node (.hole middle.tree) c) +
        auxiliaryPotential middle - auxiliaryPotential s ≤ 3 * Real.logb 2 s.size + 1 :=
  auxiliary_cut_prefix s j valid

/-- Merge the leftmost attached component using one minimum splay. -/
theorem join_front (s middle : Region) (nonempty : 0 < s.size)
    (attached : s.fringe.head? = some middle.tree) :
    ∃ c : Region, ∃ cost,
      c.size + 1 = s.size ∧ s.fringe = (Pointer.Lazy.Skeleton.node (.hole middle.tree) c).fringe ∧
      Rotations s.tree (.node middle.tree c.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node middle c) - auxiliaryPotential s - auxiliaryPotential middle ≤
        3 * Real.logb 2 (s.size + middle.size : Nat) + 1 :=
  auxiliary_join_front s middle nonempty attached

end RotationBST.Tango.Auxiliary.Results

/-- info: abstract audit passed for `RotationBST.Tango.Auxiliary.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Auxiliary.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces, RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract, RotationBST.Algorithms.Splay.Potential.Abstract, RotationBST.Models.Region.Defs]
