module

public import RotationBST.Tango.State.Nesting.Edits.Realization

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem positive_region {s : MarkedTree} (nonempty : s ≠ .nil) : 0 < s.region.size := by
  cases s with
  | nil => contradiction
  | node l r cl cr => simp [region, Pointer.Lazy.Skeleton.size]

private theorem positive_side (s : MarkedTree) (cut : Bool) :
    0 < (if cut then [s.nesting] else s.nesting.fringe).length := by
  cases cut <;> simp [nesting_fringe_length]

/-- A marked reference edge cuts exactly the descendant path's fringe interval. -/
theorem left_edge_cut (l r : MarkedTree) (cr : Bool) (nonempty : l ≠ .nil) :
    ComponentNesting.Cut (MarkedTree.node l r false cr).nesting (MarkedTree.node l r true cr).nesting := by
  have small := positive_region nonempty
  have other := positive_side r cr
  have h := ComponentNesting.Cut.interval [] l.nesting.fringe
    (if cr then [r.nesting] else r.nesting.fringe)
    (by rw [nesting_fringe_length]; omega) (by simpa only [List.length_nil, Nat.zero_add] using other)
  have branch := nesting_branch l nonempty
  simpa only [List.nil_append, nesting, Bool.false_eq_true, ite_false, ite_true, ← branch] using h

theorem right_edge_cut (l r : MarkedTree) (cl : Bool) (nonempty : r ≠ .nil) :
    ComponentNesting.Cut (MarkedTree.node l r cl false).nesting (MarkedTree.node l r cl true).nesting := by
  have small := positive_region nonempty
  have other := positive_side l cl
  have h := ComponentNesting.Cut.interval (if cl then [l.nesting] else l.nesting.fringe)
    r.nesting.fringe [] (by rw [nesting_fringe_length]; omega)
    (by simpa only [List.length_nil, Nat.add_zero] using other)
  have branch := nesting_branch r nonempty
  simpa only [List.append_nil, nesting, Bool.false_eq_true, ite_false, ite_true, ← branch] using h

end RotationBST.Tango.MarkedTree
