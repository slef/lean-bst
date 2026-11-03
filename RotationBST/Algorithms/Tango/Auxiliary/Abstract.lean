module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Auxiliary.AbstractBridge

@[expose] public section
namespace RotationBST.Tango.Auxiliary.Results
open Geometric Geometric.Region

/-- Auxiliary splaying preserves every attached subtree and serves the selected
global key. Its amortized cost depends only on the active auxiliary size. -/
theorem access (s : Region) (x : Nat) (valid : x ∈ s.keys 0) :
    let result := auxiliaryRun s (index s 0 x)
    s.fringe = result.1.fringe ∧ Access s.tree result.1.tree x result.2 ∧
      (result.2 : ℝ) + auxiliaryPotential result.1 - auxiliaryPotential s ≤
        3 * Real.logb 2 s.size + 1 :=
  ⟨(auxiliaryRun_correct s _ (index_valid valid)).2.1, auxiliaryRun_access s x valid,
    auxiliaryRun_bound s _ (index_valid valid)⟩

/-- Mark a suffix as a separate component, retaining all keys in the BST. -/
theorem split (s : Region) (k : Nat) (positive : 0 < k) (valid : k ≤ s.size) :
    ∃ a b : Region, ∃ cost,
      a.size + 1 = k ∧ a.size + b.size + 1 = s.size ∧
      s.fringe = (Pointer.Lazy.Skeleton.node a b).fringe ∧
      Rotations s.tree (.node a.tree b.tree) cost ∧
      (cost : ℝ) + auxiliaryPotential (.node a (.hole b.tree)) + auxiliaryPotential b - auxiliaryPotential s ≤
        3 * Real.logb 2 s.size + 1 := auxiliary_cut_suffix s k positive valid

/-- Merge adjacent components, including their actual rotations in the BST. -/
theorem join (left right : Region) (attached : left.fringe.getLast? = some right.tree) :
    ∃ u cost, u.fringe = left.fringe.dropLast ++ right.fringe ∧
      Rotations left.tree u.tree cost ∧
      (cost : ℝ) + auxiliaryPotential u - auxiliaryPotential left - auxiliaryPotential right ≤
        3 * Real.logb 2 (left.size + right.size : Nat) + 1 := auxiliary_join_bound left right attached

end RotationBST.Tango.Auxiliary.Results

/-- info: abstract audit passed for `RotationBST.Tango.Auxiliary.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Auxiliary.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces, RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract, RotationBST.Algorithms.Splay.Potential.Abstract]
