module

public import RotationBST.Tango.State.Context.Lookup.Update
public import RotationBST.Tango.State.Nesting.Matching

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- A fixed executable local edit transfers to the matching fringe component
without any choice of a context or resulting state. -/
theorem editFringe_nesting (s reference child : MarkedTree) (target : ComponentNesting) (i : Nat) (bound : ℝ)
    (edit : MarkedTree → MarkedTree × Nat) (same : s.nesting = reference.nesting)
    (atIndex : reference.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      (edit actual).1.nesting = target ∧
        Rotations actual.tree (edit actual).1.tree (edit actual).2 ∧
        ((edit actual).2 : ℝ) + (edit actual).1.potential - actual.potential ≤ bound) :
    (Context.editFringe s i edit).1.nesting = .branch (reference.nesting.fringe.set i target) ∧
      Rotations s.tree (Context.editFringe s i edit).1.tree (Context.editFringe s i edit).2 ∧
      ((Context.editFringe s i edit).2 : ℝ) + (Context.editFringe s i edit).1.potential - s.potential ≤ bound := by
  have matching := nesting_fringe_matching same
  obtain ⟨hi, hc⟩ := List.getElem?_eq_some_iff.mp atIndex
  have hs : i < s.fringe.length := by rw [matching.length_eq]; exact hi
  let actual := s.fringe[i]
  have nested : actual.nesting = child.nesting := by
    have h := matching.get hs hi
    simpa only [List.get_eq_getElem, hc] using h
  have actualNonempty : actual ≠ .nil := by
    intro empty
    have h : child.nesting = ComponentNesting.empty := by rw [← nested, empty]; rfl
    cases child with
    | nil => contradiction
    | node l r cl cr => cases h
  obtain ⟨targetNesting, rotations, estimate⟩ := localUpdate actual nested
  obtain ⟨cost, _, resultNesting, wholeRotations, difference⟩ :=
    Context.editFringe_spec s actual i edit (List.getElem?_eq_getElem hs) actualNonempty rotations
  refine ⟨?_, wholeRotations, ?_⟩
  · rw [resultNesting, ← nesting_fringe, same, targetNesting]
  · rw [cost]
    linarith

theorem editFringe_simulates (s reference child target : MarkedTree) (i : Nat) (bound : ℝ)
    (edit : MarkedTree → MarkedTree × Nat) (same : s.nesting = reference.nesting)
    (atIndex : reference.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      (edit actual).1.nesting = target.nesting ∧
        Rotations actual.tree (edit actual).1.tree (edit actual).2 ∧
        ((edit actual).2 : ℝ) + (edit actual).1.potential - actual.potential ≤ bound) :
    (Context.editFringe s i edit).1.nesting = .branch (reference.nesting.fringe.set i target.nesting) ∧
      Rotations s.tree (Context.editFringe s i edit).1.tree (Context.editFringe s i edit).2 ∧
      ((Context.editFringe s i edit).2 : ℝ) + (Context.editFringe s i edit).1.potential - s.potential ≤ bound :=
  editFringe_nesting s reference child target.nesting i bound edit same atIndex nonempty localUpdate

end RotationBST.Tango.MarkedTree
