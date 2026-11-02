module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.ComponentPath.Edits

@[expose] public section
namespace RotationBST.Tango.State.ComponentPath.Results
open MarkedTree

theorem cut (s reference child : MarkedTree) (path : List Nat) (i j : Nat)
    (same : s.nesting = reference.nesting) (found : reference.componentAt path = some child)
    (ordered : i < j) (valid : j ≤ child.region.size) (proper : j - i < child.region.size) :
    (s.editAt path (fun t => t.cutInterval i j)).1.nesting =
        reference.nesting.replaceAt path (child.nesting.group i (j - i + 1)) ∧
      Rotations s.tree (s.editAt path (fun t => t.cutInterval i j)).1.tree
        (s.editAt path (fun t => t.cutInterval i j)).2 ∧
      ((s.editAt path (fun t => t.cutInterval i j)).2 : ℝ) +
        (s.editAt path (fun t => t.cutInterval i j)).1.potential - s.potential ≤
          6 * Real.logb 2 child.region.size + 2 :=
  cut_at_path s reference child path i j same found ordered valid proper

theorem merge (s reference child attached : MarkedTree) (path : List Nat) (i : Nat)
    (same : s.nesting = reference.nesting) (found : reference.componentAt path = some child)
    (positive : 0 < child.region.size) (valid : i ≤ child.region.size)
    (slot : child.fringe[i]? = some attached) :
    (s.editAt path (fun t => t.mergeAt i)).1.nesting =
        reference.nesting.replaceAt path (child.nesting.merge i) ∧
      Rotations s.tree (s.editAt path (fun t => t.mergeAt i)).1.tree
        (s.editAt path (fun t => t.mergeAt i)).2 ∧
      ((s.editAt path (fun t => t.mergeAt i)).2 : ℝ) +
        (s.editAt path (fun t => t.mergeAt i)).1.potential - s.potential ≤
          8 * Real.logb 2 (child.region.size + attached.region.size : Nat) + 2 :=
  merge_at_path s reference child attached path i same found positive valid slot

end RotationBST.Tango.State.ComponentPath.Results

#check_bst_abstract RotationBST.Tango.State.ComponentPath.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.ComponentPath.Abstract, RotationBST.Tango.State.Context.Abstract,
  RotationBST.Tango.State.Context.Lookup.Abstract, RotationBST.Tango.State.Nesting.Abstract,
  RotationBST.Tango.State.Nesting.Edits.Abstract, RotationBST.Tango.State.Nesting.Edits.Algorithm.Abstract,
  RotationBST.Tango.State.Rebuild.Abstract, RotationBST.Tango.State.Splay.Abstract,
  RotationBST.Tango.State.Cut.Abstract, RotationBST.Tango.State.Join.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
