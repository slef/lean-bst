module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Switch

@[expose] public section
namespace RotationBST.Tango.State.PathAlgorithm.Results
open MarkedTree Context

theorem mark (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark false) :: fs) child).nesting) :
    (s.markInPath fs f child).1.nesting = (plug ((f.setMark true) :: fs) child).nesting ∧
      Rotations s.tree (s.markInPath fs f child).1.tree (s.markInPath fs f child).2 ∧
      ((s.markInPath fs f child).2 : ℝ) + (s.markInPath fs f child).1.potential - s.potential ≤
        6 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 :=
  markInPath_spec s fs unmarked f child same

theorem unmark (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree)
    (same : s.nesting = (plug ((f.setMark true) :: fs) child).nesting) :
    (s.unmarkInPath fs f).1.nesting = (plug ((f.setMark false) :: fs) child).nesting ∧
      Rotations s.tree (s.unmarkInPath fs f).1.tree (s.unmarkInPath fs f).2 ∧
      ((s.unmarkInPath fs f).2 : ℝ) + (s.unmarkInPath fs f).1.potential - s.potential ≤
        8 * Real.logb 2 (plug ((f.setMark false) :: fs) child).region.size + 2 :=
  unmarkInPath_spec s fs unmarked f child same

theorem switch_preference (s : MarkedTree) (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (plug fs (.node l r (!left) left)).nesting)
    (beforeBound : (plug fs (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (plug fs (.node l r left (!left))).region.size ≤ H) :
    (s.switchInPath fs l r left).1.nesting = (plug fs (.node l r left (!left))).nesting ∧
      Rotations s.tree (s.switchInPath fs l r left).1.tree (s.switchInPath fs l r left).2 ∧
      ((s.switchInPath fs l r left).2 : ℝ) + (s.switchInPath fs l r left).1.potential - s.potential ≤
        14 * Real.logb 2 H + 4 :=
  switchInPath_spec s fs unmarked l r left H same beforeBound afterBound

end RotationBST.Tango.State.PathAlgorithm.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.PathAlgorithm.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.PathAlgorithm.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Context.Defs, RotationBST.Algorithms.Tango.State.Context.Fringe.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs, RotationBST.Algorithms.Tango.State.Nesting.Edits.Path.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Defs,
  RotationBST.Algorithms.Tango.State.Rebuild.Defs, RotationBST.Algorithms.Tango.State.Splay.Defs,
  RotationBST.Algorithms.Tango.State.Cut.Defs, RotationBST.Algorithms.Tango.State.Join.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract, RotationBST.Models.Region.Defs, RotationBST.Algorithms.Tango.State.Abstract]
