module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- Retained smaller-key siblings are already in place in the full maximum
view; exposing a focused last-child interval requires no initialization. -/
theorem maximumEnclosingView_eq (fs : List Frame) (focus : Multiway)
    (right : ∀ f ∈ fs, IsRightFrame f) :
    (maximumView (plug fs focus)).tree = maximumEnclosingView focus fs := by
  induction fs generalizing focus with
  | nil => rfl
  | cons f fs ih =>
    have head := right f (List.mem_cons_self ..)
    have tail := ih (f.fill focus) (fun g hg => right g (List.mem_cons_of_mem _ hg))
    simp only [plug, tail, maximumEnclosingView, maximumContextRemainder]
    cases rest : maximumContextRemainder fs <;>
      cases f <;> simp only [IsRightFrame] at head
    all_goals simp [maximumFrameRemainder, Frame.fill, maximumView,
      MaximumView.tree, maximumOpenView, leftComb_append, leftComb]

end RotationBST.SplitTree.Multiway.Finger
