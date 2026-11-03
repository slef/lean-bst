module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.ComponentPath.Edits

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
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.ComponentPath.Defs, RotationBST.Algorithms.Tango.State.Context.Defs,
  RotationBST.Algorithms.Tango.State.Context.Lookup.Defs, RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Defs, RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs, RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs, RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
