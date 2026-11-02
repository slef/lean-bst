module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Nesting.Edits.Path

@[expose] public section
namespace RotationBST.Tango.State.PathEdits.Results

/-! Mark and preference changes anywhere within a preferred component. The
unmarked context stays inside that component; marked boundaries are handled
by the separate whole-tree embedding theorem. -/

theorem mark_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug fs ((f.setMark false).fill child)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs ((f.setMark true).fill child)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        6 * Real.logb 2 (Context.plug fs ((f.setMark false).fill child)).region.size + 2 :=
  Tango.mark_in_path fs unmarked f child s same

theorem unmark_in_path (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug fs ((f.setMark true).fill child)).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs ((f.setMark false).fill child)).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (Context.plug fs ((f.setMark false).fill child)).region.size + 2 :=
  Tango.unmark_in_path fs unmarked f child s same

theorem switch_in_path_bound (fs : List Context.Frame) (unmarked : ∀ f ∈ fs, f.marked = false)
    (s l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (Context.plug fs (.node l r (!left) left)).nesting)
    (beforeBound : (Context.plug fs (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (Context.plug fs (.node l r left (!left))).region.size ≤ H) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug fs (.node l r left (!left))).nesting ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 :=
  Tango.switch_in_path_bound fs unmarked s l r left H same beforeBound afterBound

end RotationBST.Tango.State.PathEdits.Results

#check_bst_abstract RotationBST.Tango.State.PathEdits.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Nesting.Abstract, RotationBST.Tango.State.Context.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
