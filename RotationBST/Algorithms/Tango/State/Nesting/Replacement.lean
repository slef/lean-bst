module

public import RotationBST.Algorithms.Tango.State.Context.Replacement
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Lists
public import RotationBST.Algorithms.Tango.State.Context.Fringe

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Transfer an update of a reference fringe component to the corresponding
component of any BST with the same nesting. The surrounding auxiliary shape
contributes no additional rotations or amortized cost. -/
theorem simulate_fringe_update (s reference child target : MarkedTree) (i : Nat) (bound : ℝ)
    (same : s.nesting = reference.nesting)
    (atIndex : reference.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      ∃ result : MarkedTree, ∃ cost : Nat,
        result.nesting = target.nesting ∧ Rotations actual.tree result.tree cost ∧
        (cost : ℝ) + result.potential - actual.potential ≤ bound) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = .branch (reference.nesting.fringe.set i target.nesting) ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤ bound := by
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
  obtain ⟨updated, cost, targetNesting, rotations, estimate⟩ := localUpdate actual nested
  obtain ⟨result, resultNesting, wholeRotations, difference⟩ :=
    Context.replace_fringe s actual updated i (List.getElem?_eq_getElem hs) actualNonempty rotations
  refine ⟨result, cost, ?_, wholeRotations, ?_⟩
  · rw [resultNesting, ← nesting_fringe, same, targetNesting]
  · linarith

/-- Transfer a local simulation through one marked boundary and any number of
unmarked ancestors, even when the actual enclosing auxiliary tree has a
completely different binary shape. -/
theorem simulate_boundary_segment (s child target : MarkedTree)
    (f : Context.Frame) (marked : f.marked = true) (fs : List Context.Frame)
    (unmarked : ∀ g ∈ fs, g.marked = false) (bound : ℝ)
    (same : s.nesting = (Context.plug (f :: fs) child).nesting) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      ∃ result : MarkedTree, ∃ cost : Nat,
        result.nesting = target.nesting ∧ Rotations actual.tree result.tree cost ∧
        (cost : ℝ) + result.potential - actual.potential ≤ bound) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (Context.plug (f :: fs) target).nesting ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤ bound := by
  obtain ⟨before, after, fringe⟩ := Context.boundary_fringe f marked fs unmarked
  have atIndex : (Context.plug (f :: fs) child).fringe[before.length]? = some child := by
    rw [fringe]
    simp [List.append_assoc]
  obtain ⟨result, cost, nested, rotations, estimate⟩ :=
    simulate_fringe_update s (Context.plug (f :: fs) child) child target before.length bound
      same atIndex nonempty localUpdate
  refine ⟨result, cost, nested.trans ?_, rotations, estimate⟩
  rw [nesting_branch (Context.plug (f :: fs) target) (Context.plug_nonempty _ _ (by simp))]
  rw [nesting_fringe, nesting_fringe, fringe, fringe]
  simp [List.map_append, List.append_assoc]

end RotationBST.Tango.MarkedTree
