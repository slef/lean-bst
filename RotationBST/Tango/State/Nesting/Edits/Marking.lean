module

public import RotationBST.Tango.State.Nesting.Edits.Lists

@[expose] public section
namespace RotationBST.Tango.MarkedTree

private theorem side_length (s : MarkedTree) (cut : Bool) :
    (if cut then [s.nesting] else s.nesting.fringe).length =
      (if cut then 0 else s.region.size) + 1 := by
  cases cut <;> simp [nesting_fringe_length]

theorem mark_left_nesting (l r : MarkedTree) (cr : Bool) (nonempty : l ≠ .nil) :
    (MarkedTree.node l r true cr).nesting =
      (MarkedTree.node l r false cr).nesting.group 0 (l.region.size + 1) := by
  have h := ComponentNesting.group_append [] l.nesting.fringe (if cr then [r.nesting] else r.nesting.fringe)
  simp only [List.nil_append, List.length_nil, nesting_fringe_length] at h
  change ComponentNesting.branch ([l.nesting] ++ (if cr then [r.nesting] else r.nesting.fringe)) = _
  rw [show (MarkedTree.node l r false cr).nesting =
    .branch (l.nesting.fringe ++ (if cr then [r.nesting] else r.nesting.fringe)) from rfl, h]
  rw [← nesting_branch l nonempty]

theorem mark_right_nesting (l r : MarkedTree) (cl : Bool) (nonempty : r ≠ .nil) :
    (MarkedTree.node l r cl true).nesting =
      (MarkedTree.node l r cl false).nesting.group
        ((if cl then 0 else l.region.size) + 1) (r.region.size + 1) := by
  have h := ComponentNesting.group_append (if cl then [l.nesting] else l.nesting.fringe) r.nesting.fringe []
  simp only [List.append_nil, side_length, nesting_fringe_length] at h
  change ComponentNesting.branch ((if cl then [l.nesting] else l.nesting.fringe) ++ [r.nesting]) = _
  rw [show (MarkedTree.node l r cl false).nesting =
    .branch ((if cl then [l.nesting] else l.nesting.fringe) ++ r.nesting.fringe) from rfl, h]
  rw [← nesting_branch r nonempty]

theorem mark_middle_nesting (a middle c : MarkedTree) (ca cc : Bool) (nonempty : middle ≠ .nil) :
    (MarkedTree.node a (.node middle c true cc) ca false).nesting =
      (MarkedTree.node a (.node middle c false cc) ca false).nesting.group
        ((if ca then 0 else a.region.size) + 1) (middle.region.size + 1) := by
  have h := ComponentNesting.group_append (if ca then [a.nesting] else a.nesting.fringe)
    middle.nesting.fringe (if cc then [c.nesting] else c.nesting.fringe)
  simp only [side_length, nesting_fringe_length] at h
  rw [← nesting_branch middle nonempty] at h
  simpa only [nesting, Bool.false_eq_true, ite_false, ite_true, ComponentNesting.fringe,
    List.append_assoc] using h.symm

/-- Removing a mark expands exactly one component's fringe slots. -/
theorem unmark_left_nesting (l r : MarkedTree) (cr : Bool) :
    (MarkedTree.node l r false cr).nesting = (MarkedTree.node l r true cr).nesting.merge 0 := by
  have h := ComponentNesting.merge_append [] (if cr then [r.nesting] else r.nesting.fringe) l.nesting
  simpa only [List.nil_append, List.length_nil, nesting, Bool.false_eq_true, ite_false, ite_true] using h.symm

theorem unmark_right_nesting (l r : MarkedTree) (cl : Bool) :
    (MarkedTree.node l r cl false).nesting = (MarkedTree.node l r cl true).nesting.merge
      ((if cl then 0 else l.region.size) + 1) := by
  have h := ComponentNesting.merge_append (if cl then [l.nesting] else l.nesting.fringe) [] r.nesting
  simpa only [List.append_nil, side_length, nesting, Bool.false_eq_true, ite_false, ite_true] using h.symm

theorem unmark_middle_nesting (a middle c : MarkedTree) (ca cc : Bool) :
    (MarkedTree.node a (.node middle c false cc) ca false).nesting =
      (MarkedTree.node a (.node middle c true cc) ca false).nesting.merge
        ((if ca then 0 else a.region.size) + 1) := by
  have h := ComponentNesting.merge_append (if ca then [a.nesting] else a.nesting.fringe)
    (if cc then [c.nesting] else c.nesting.fringe) middle.nesting
  simp only [side_length] at h
  simpa only [nesting, Bool.false_eq_true, ite_false, ite_true, ComponentNesting.fringe,
    List.append_assoc] using h.symm

end RotationBST.Tango.MarkedTree
