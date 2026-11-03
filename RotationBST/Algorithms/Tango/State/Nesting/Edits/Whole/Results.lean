module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Whole

@[expose] public section
namespace RotationBST.Tango.State.WholeEdits.Results

theorem switch_in_component (outer : List Context.Frame) (boundary : Context.Boundary outer)
    (inner : List Context.Frame) (unmarked : ∀ f ∈ inner, f.marked = false)
    (s l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (Context.plug outer (Context.plug inner (.node l r (!left) left))).nesting)
    (beforeBound : (Context.plug inner (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (Context.plug inner (.node l r left (!left))).region.size ≤ H) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug outer (Context.plug inner (.node l r left (!left)))).nesting ∧
      Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 :=
  Tango.switch_in_component outer boundary inner unmarked s l r left H same beforeBound afterBound

theorem unmark_in_component (outer : List Context.Frame) (boundary : Context.Boundary outer)
    (inner : List Context.Frame) (unmarked : ∀ g ∈ inner, g.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug outer (Context.plug inner ((f.setMark true).fill child))).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug outer (Context.plug inner ((f.setMark false).fill child))).nesting ∧
      Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (Context.plug inner ((f.setMark false).fill child)).region.size + 2 :=
  Tango.unmark_in_component outer boundary inner unmarked f child s same

end RotationBST.Tango.State.WholeEdits.Results

#check_bst_abstract RotationBST.Tango.State.WholeEdits.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs, RotationBST.Algorithms.Tango.State.Context.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
