module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Root

@[expose] public section
namespace RotationBST.Tango.State.Edits.Results
open MarkedTree

/-! Realization of nesting edits and root preference changes by actual BST
rotations. The bounds use the potential of the full marked state. -/

theorem simulate_cut (s reference : MarkedTree) (same : s.nesting = reference.nesting)
    (i j : Nat) (ordered : i < j) (valid : j ≤ reference.region.size)
    (proper : j - i < reference.region.size) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = reference.nesting.group i (j - i + 1) ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 reference.region.size + 2 :=
  MarkedTree.simulate_cut s reference same i j ordered valid proper

theorem simulate_merge (s reference child : MarkedTree) (same : s.nesting = reference.nesting)
    (i : Nat) (positive : 0 < reference.region.size) (valid : i ≤ reference.region.size)
    (attached : reference.fringe[i]? = some child) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = reference.nesting.merge i ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (reference.region.size + child.region.size : Nat) + 2 :=
  MarkedTree.simulate_merge s reference child same i positive valid attached

theorem attach_left (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r false true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 8 * Real.logb 2 (l.region.size + 1 : Nat) + 2 :=
  MarkedTree.attach_left s l r same

theorem attach_right (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true false).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 8 * Real.logb 2 (r.region.size + 1 : Nat) + 2 :=
  MarkedTree.attach_right s l r same

theorem switch_right (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r false true).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r true false).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        14 * Real.logb 2 (l.region.size + r.region.size + 1 : Nat) + 4 :=
  MarkedTree.switch_right s l r same

theorem switch_left (s l r : MarkedTree) (same : s.nesting = (MarkedTree.node l r true false).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (MarkedTree.node l r false true).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        14 * Real.logb 2 (l.region.size + r.region.size + 1 : Nat) + 4 :=
  MarkedTree.switch_left s l r same

end RotationBST.Tango.State.Edits.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.Edits.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.Edits.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs, RotationBST.Algorithms.Tango.State.Nesting.Edits.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
