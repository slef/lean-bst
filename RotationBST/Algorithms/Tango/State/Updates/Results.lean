module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Join

@[expose] public section
namespace RotationBST.Tango.State.Updates.Results
open MarkedTree

/-! Actual marked-state updates and their full-BST rotation costs. Connecting
these operations to successive preferred-path partitions is a separate obligation. -/

theorem cut_prefix (s : MarkedTree) (j : Nat) (positive : 0 < j) (valid : j < s.region.size) :
    ∃ l r : MarkedTree, ∃ cr : Bool, ∃ cost : Nat,
      l.region.size = j ∧ s.fringe = (MarkedTree.node l r false cr).fringe ∧
      Rotations s.tree (MarkedTree.node l r true cr).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l r true cr).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 :=
  MarkedTree.cut_prefix s j positive valid

theorem cut_suffix (s : MarkedTree) (i : Nat) (positive : 0 < i) (valid : i < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl : Bool, ∃ cost : Nat,
      (if cl then 0 else l.region.size) + 1 = i ∧
      r.region.size = s.region.size - i ∧
      s.fringe = (MarkedTree.node l r cl false).fringe ∧
      Rotations s.tree (MarkedTree.node l r cl true).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l r cl true).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 :=
  MarkedTree.cut_suffix s i positive valid

theorem cut_interior (s : MarkedTree) (i j : Nat)
    (positive : 0 < i) (ordered : i < j) (interior : j < s.region.size) :
    ∃ a middle c : MarkedTree, ∃ ca cc : Bool, ∃ cost : Nat,
      (if ca then 0 else a.region.size) + 1 = i ∧ middle.region.size = j - i ∧
      s.fringe = (MarkedTree.node a (.node middle c false cc) ca false).fringe ∧
      Rotations s.tree (MarkedTree.node a (.node middle c true cc) ca false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node a (.node middle c true cc) ca false).potential - s.potential ≤
        6 * Real.logb 2 s.region.size + 2 :=
  MarkedTree.cut_interior s i j positive ordered interior

theorem join_back (s right : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.getLast? = some right) :
    ∃ l : MarkedTree, ∃ cl : Bool, ∃ cost : Nat,
      s.fringe = (MarkedTree.node l right cl true).fringe ∧
      Rotations s.tree (MarkedTree.node l right cl false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l right cl false).potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + right.region.size : Nat) + 1 :=
  MarkedTree.join_back s right positive attached

theorem join_front (s left : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.head? = some left) :
    ∃ r : MarkedTree, ∃ cr : Bool, ∃ cost : Nat,
      s.fringe = (MarkedTree.node left r true cr).fringe ∧
      Rotations s.tree (MarkedTree.node left r false cr).tree cost ∧
      (cost : ℝ) + (MarkedTree.node left r false cr).potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + left.region.size : Nat) + 1 :=
  MarkedTree.join_front s left positive attached

theorem join_interior (s middle : MarkedTree) (i : Nat)
    (positive : 0 < i) (interior : i < s.region.size)
    (attached : s.fringe[i]? = some middle) :
    ∃ a c : MarkedTree, ∃ ca cc : Bool, ∃ cost : Nat,
      (if ca then 0 else a.region.size) + 1 = i ∧
      s.fringe = (MarkedTree.node a (.node middle c true cc) ca false).fringe ∧
      Rotations s.tree (MarkedTree.node a (.node middle c false cc) ca false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node a (.node middle c false cc) ca false).potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + middle.region.size : Nat) + 2 :=
  MarkedTree.join_interior s middle i positive interior attached

end RotationBST.Tango.State.Updates.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.Updates.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.Updates.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract, RotationBST.Models.Region.Defs, RotationBST.Bounds.Interleave.Wilber.Defs, RotationBST.Algorithms.Tango.State.Abstract, RotationBST.Bounds.Interleave.Transition.Defs]
