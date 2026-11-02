module

public import RotationBST.Tango.State.Context.Replacement
public import RotationBST.Tango.State.Context.Fringe.Exact

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- Traversing only unmarked edges places the focused component's fringe in a
fixed contiguous interval of the enclosing component's fringe. -/
theorem unmarked_fringe (fs : List Frame) (unmarked : ∀ f ∈ fs, f.marked = false) :
    ∃ before after : List MarkedTree,
      ∀ s, (plug fs s).fringe = before ++ s.fringe ++ after := by
  exact ⟨before fs, after fs, unmarked_fringe_exact fs unmarked⟩

/-- A marked edge followed by unmarked ancestors selects one exact fringe slot,
independently of the tree substituted into that slot. -/
theorem boundary_fringe (f : Frame) (marked : f.marked = true) (fs : List Frame)
    (unmarked : ∀ g ∈ fs, g.marked = false) :
    ∃ before after : List MarkedTree,
      ∀ s, (plug (f :: fs) s).fringe = before ++ [s] ++ after := by
  exact ⟨before (f :: fs), after (f :: fs), boundary_fringe_exact f marked fs unmarked⟩

end RotationBST.Tango.Context
