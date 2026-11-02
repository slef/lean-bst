module

public import RotationBST.Tango.State.Context.Fringe.Exact
public import RotationBST.Tango.State.Context.Replacement
public import RotationBST.Tango.State.Nesting.Edits.Lists

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

private theorem marked_setMark (f : Frame) (mark : Bool) : (f.setMark mark).marked = mark := by
  cases f <;> rfl

/-- Exact component signatures on both sides of a reference-edge mark change.
The computed prefix is the same for the cut and the inverse merge. -/
theorem edge_nesting (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree) :
    (plug ((f.setMark false) :: fs) child).nesting =
      .branch ((before (f :: fs)).map nesting ++ child.nesting.fringe ++ (after (f :: fs)).map nesting) ∧
    (plug ((f.setMark true) :: fs) child).nesting =
      .branch ((before (f :: fs)).map nesting ++ [child.nesting] ++ (after (f :: fs)).map nesting) := by
  have hu : ∀ g ∈ (f.setMark false) :: fs, g.marked = false := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact marked_setMark f false
    · exact unmarked g hg
  have source := unmarked_fringe_exact ((f.setMark false) :: fs) hu child
  have target := boundary_fringe_exact (f.setMark true) (marked_setMark f true) fs unmarked child
  simp only [before, after, Frame.before_setMark, Frame.after_setMark] at source target ⊢
  constructor
  · rw [nesting_branch _ (plug_nonempty _ _ (by simp)), nesting_fringe, source]
    simp only [List.map_append, ← nesting_fringe]
  · rw [nesting_branch _ (plug_nonempty _ _ (by simp)), nesting_fringe, target]
    simp only [List.map_append, List.map_singleton]

/-- An edge cut is the group at the computed active-rank offset. -/
theorem mark_path_group (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree) (nonempty : child ≠ .nil) :
    (plug ((f.setMark true) :: fs) child).nesting =
      (plug ((f.setMark false) :: fs) child).nesting.group
        (before (f :: fs)).length (child.region.size + 1) := by
  obtain ⟨source, target⟩ := edge_nesting fs unmarked f child
  rw [source, target]
  have h := ComponentNesting.group_append ((before (f :: fs)).map nesting) child.nesting.fringe
    ((after (f :: fs)).map nesting)
  rw [List.length_map, nesting_fringe_length] at h
  rw [← nesting_branch child nonempty] at h
  exact h.symm

/-- The inverse edge change merges the component at that same computed slot. -/
theorem unmark_path_merge (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree) :
    (plug ((f.setMark false) :: fs) child).nesting =
      (plug ((f.setMark true) :: fs) child).nesting.merge (before (f :: fs)).length := by
  obtain ⟨source, target⟩ := edge_nesting fs unmarked f child
  rw [source, target]
  simpa only [List.length_map] using
    (ComponentNesting.merge_append ((before (f :: fs)).map nesting)
      ((after (f :: fs)).map nesting) child.nesting).symm

/-- A focused edge always leaves its parent component nonempty. -/
theorem edge_remaining (f : Frame) (fs : List Frame) :
    0 < (before (f :: fs)).length + (after (f :: fs)).length := by
  have frame : 0 < f.before.length + f.after.length := by
    cases f with
    | left r cl cr =>
      have h := marked_fringe_length r
      cases cr <;> simp [Frame.before, Frame.after, h]
    | right l cr cl =>
      have h := marked_fringe_length l
      cases cl <;> simp [Frame.before, Frame.after, h]
  simp only [before, after, List.length_append]
  omega

/-- Exact active sizes before and after marking the focused edge. -/
theorem edge_sizes (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree) :
    (plug ((f.setMark false) :: fs) child).region.size =
      (before (f :: fs)).length + child.region.size + (after (f :: fs)).length ∧
    (plug ((f.setMark true) :: fs) child).region.size =
      (before (f :: fs)).length + (after (f :: fs)).length := by
  obtain ⟨source, target⟩ := edge_nesting fs unmarked f child
  have hs := congrArg (fun n : ComponentNesting => n.fringe.length) source
  have ht := congrArg (fun n : ComponentNesting => n.fringe.length) target
  rw [nesting_fringe_length] at hs ht
  change _ = (((before (f :: fs)).map nesting ++ child.nesting.fringe) ++
    (after (f :: fs)).map nesting).length at hs
  rw [List.length_append, List.length_append, nesting_fringe_length] at hs
  simp only [List.length_map] at hs
  simp only [ComponentNesting.fringe, List.length_append, List.length_map, List.length_singleton] at ht
  omega

/-- The computed edge index selects the focused marked child. -/
theorem edge_slot (fs : List Frame) (unmarked : ∀ g ∈ fs, g.marked = false)
    (f : Frame) (child : MarkedTree) :
    (plug ((f.setMark true) :: fs) child).fringe[(before (f :: fs)).length]? = some child := by
  rw [boundary_fringe_exact (f.setMark true) (marked_setMark f true) fs unmarked child]
  simp [before, after, List.append_assoc]

end RotationBST.Tango.Context
