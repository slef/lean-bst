module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Cut.Interior

@[expose] public section
namespace RotationBST.Tango.State.Cuts.Results
open MarkedTree

theorem prefix_cut (s : MarkedTree) (count : Nat)
    (positive : 0 < count) (valid : count < s.region.size) :
    ∃ l r : MarkedTree, ∃ cr : Bool,
      (s.cutPrefix count).1 = .node l r true cr ∧ l.region.size = count ∧
      s.fringe = (MarkedTree.node l r false cr).fringe ∧
      Rotations s.tree (s.cutPrefix count).1.tree (s.cutPrefix count).2 ∧
      ((s.cutPrefix count).2 : ℝ) + (s.cutPrefix count).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 :=
  cutPrefix_spec s count positive valid

theorem suffix (s : MarkedTree) (first : Nat)
    (positive : 0 < first) (valid : first < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl : Bool,
      (s.cutSuffix first).1 = .node l r cl true ∧
      (if cl then 0 else l.region.size) + 1 = first ∧
      r.region.size = s.region.size - first ∧
      s.fringe = (MarkedTree.node l r cl false).fringe ∧
      Rotations s.tree (s.cutSuffix first).1.tree (s.cutSuffix first).2 ∧
      ((s.cutSuffix first).2 : ℝ) + (s.cutSuffix first).1.potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 :=
  cutSuffix_spec s first positive valid

theorem interior (s : MarkedTree) (first pastLast : Nat)
    (positive : 0 < first) (ordered : first < pastLast) (interior : pastLast < s.region.size) :
    ∃ a middle c : MarkedTree, ∃ ca cc : Bool,
      (s.cutInterior first pastLast).1 = .node a (.node middle c true cc) ca false ∧
      (if ca then 0 else a.region.size) + 1 = first ∧ middle.region.size = pastLast - first ∧
      s.fringe = (MarkedTree.node a (.node middle c false cc) ca false).fringe ∧
      Rotations s.tree (s.cutInterior first pastLast).1.tree (s.cutInterior first pastLast).2 ∧
      ((s.cutInterior first pastLast).2 : ℝ) + (s.cutInterior first pastLast).1.potential - s.potential ≤
        6 * Real.logb 2 s.region.size + 2 :=
  cutInterior_spec s first pastLast positive ordered interior

end RotationBST.Tango.State.Cuts.Results

#check_bst_abstract RotationBST.Tango.State.Cuts.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Tango.State.Join.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
