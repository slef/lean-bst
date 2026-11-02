module

public import RotationBST.Tango.State.Context.Fringe.Abstract
public import RotationBST.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

@[simp] theorem Frame.before_setMark (f : Frame) (mark : Bool) : (f.setMark mark).before = f.before := by
  cases f <;> rfl

@[simp] theorem Frame.after_setMark (f : Frame) (mark : Bool) : (f.setMark mark).after = f.after := by
  cases f <;> rfl

theorem Frame.fill_fringe (f : Frame) (s : MarkedTree) :
    (f.fill s).fringe = f.before ++ (if f.marked then [s] else s.fringe) ++ f.after := by
  cases f <;> simp [Frame.fill, Frame.before, Frame.after, Frame.marked, fringe] <;> rfl

/-- The computed prefix and suffix give the exact fringe decomposition along
an unmarked reference path. -/
theorem unmarked_fringe_exact (fs : List Frame) (unmarked : ∀ f ∈ fs, f.marked = false) (s : MarkedTree) :
    (plug fs s).fringe = before fs ++ s.fringe ++ after fs := by
  induction fs generalizing s with
  | nil => simp [plug, before, after]
  | cons f fs ih =>
    have mark := unmarked f (List.mem_cons_self ..)
    have tail := fun g hg => unmarked g (List.mem_cons_of_mem _ hg)
    simpa only [plug, before, after, Frame.fill_fringe, mark, Bool.false_eq_true,
      ite_false, List.append_assoc] using ih tail (f.fill s)

/-- The exact slot of a marked child under unmarked ancestors is the length of
the computed fringe prefix. -/
theorem boundary_fringe_exact (f : Frame) (marked : f.marked = true) (fs : List Frame)
    (unmarked : ∀ g ∈ fs, g.marked = false) (s : MarkedTree) :
    (plug (f :: fs) s).fringe = before (f :: fs) ++ [s] ++ after (f :: fs) := by
  simpa only [plug, before, after, Frame.fill_fringe, marked, ite_true, List.append_assoc] using
    unmarked_fringe_exact fs unmarked (f.fill s)

end RotationBST.Tango.Context
