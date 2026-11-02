module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Join.Interior

@[expose] public section
namespace RotationBST.Tango.State.Joins.Results
open MarkedTree

theorem back (s right : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.getLast? = some right) :
    ∃ l : MarkedTree, ∃ cl : Bool,
      s.joinBack.1 = .node l right cl false ∧
      s.fringe = (MarkedTree.node l right cl true).fringe ∧
      Rotations s.tree s.joinBack.1.tree s.joinBack.2 ∧
      (s.joinBack.2 : ℝ) + s.joinBack.1.potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + right.region.size : Nat) + 1 :=
  joinBack_spec s right positive attached

theorem front (s left : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.head? = some left) :
    ∃ r : MarkedTree, ∃ cr : Bool,
      s.joinFront.1 = .node left r false cr ∧
      s.fringe = (MarkedTree.node left r true cr).fringe ∧
      Rotations s.tree s.joinFront.1.tree s.joinFront.2 ∧
      (s.joinFront.2 : ℝ) + s.joinFront.1.potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + left.region.size : Nat) + 1 :=
  joinFront_spec s left positive attached

theorem interior (s middle : MarkedTree) (i : Nat)
    (positive : 0 < i) (interior : i < s.region.size)
    (attached : s.fringe[i]? = some middle) :
    ∃ a c : MarkedTree, ∃ ca cc : Bool,
      (s.joinInterior i).1 = .node a (.node middle c false cc) ca false ∧
      (if ca then 0 else a.region.size) + 1 = i ∧
      s.fringe = (MarkedTree.node a (.node middle c true cc) ca false).fringe ∧
      Rotations s.tree (s.joinInterior i).1.tree (s.joinInterior i).2 ∧
      ((s.joinInterior i).2 : ℝ) + (s.joinInterior i).1.potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + middle.region.size : Nat) + 2 :=
  joinInterior_spec s middle i positive interior attached

end RotationBST.Tango.State.Joins.Results

#check_bst_abstract RotationBST.Tango.State.Joins.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Tango.State.Join.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
