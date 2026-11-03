module

public import RotationBST.Algorithms.Tango.State.Nesting.Context
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Path

@[expose] public section
namespace RotationBST.Tango
open MarkedTree

/-- Switch a preference inside any component of the full BST. The inner
unmarked context identifies the affected preferred path; the outer context may
cross arbitrarily many marked boundaries. Only the affected component sizes
enter the amortized bound. -/
theorem switch_in_component (outer : List Context.Frame) (boundary : Context.Boundary outer)
    (inner : List Context.Frame) (unmarked : ∀ f ∈ inner, f.marked = false)
    (s l r : MarkedTree) (left : Bool) (H : Nat)
    (same : s.nesting = (Context.plug outer (Context.plug inner (.node l r (!left) left))).nesting)
    (beforeBound : (Context.plug inner (.node l r (!left) left)).region.size ≤ H)
    (afterBound : (Context.plug inner (.node l r left (!left))).region.size ≤ H) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug outer (Context.plug inner (.node l r left (!left)))).nesting ∧
      Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 14 * Real.logb 2 H + 4 := by
  apply simulate_boundary_context outer boundary s _ _ _ same
  · cases inner with
    | nil => simp [Context.plug]
    | cons f fs => exact Context.plug_nonempty _ _ (by simp)
  · intro actual nested
    exact switch_in_path_bound inner unmarked actual l r left H nested beforeBound afterBound

/-- Joining an initially detached preferred child anywhere in the whole tree
has the same bound as the local join. This also covers first-time preferences. -/
theorem unmark_in_component (outer : List Context.Frame) (boundary : Context.Boundary outer)
    (inner : List Context.Frame) (unmarked : ∀ g ∈ inner, g.marked = false)
    (f : Context.Frame) (child s : MarkedTree)
    (same : s.nesting = (Context.plug outer (Context.plug inner ((f.setMark true).fill child))).nesting) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = (Context.plug outer (Context.plug inner ((f.setMark false).fill child))).nesting ∧
      Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (Context.plug inner ((f.setMark false).fill child)).region.size + 2 := by
  apply simulate_boundary_context outer boundary s _ _ _ same
  · cases inner with
    | nil => cases f <;> simp [Context.plug, Context.Frame.setMark, Context.Frame.fill]
    | cons g gs => exact Context.plug_nonempty _ _ (by simp)
  · intro actual nested
    exact unmark_in_path inner unmarked f child actual nested

end RotationBST.Tango
