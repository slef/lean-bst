module

public import RotationBST.Algorithms.Tango.State.Nesting.Replacement
public import RotationBST.Algorithms.Tango.State.Context.Split.Proofs

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Context

private theorem split_marks (fs : List Frame) :
    ∃ before after : List Frame, fs = before ++ after ∧
      (∀ f ∈ before, f.marked = false) ∧
      (after = [] ∨ ∃ f tail, after = f :: tail ∧ f.marked = true) := by
  obtain ⟨equal, unmarked, boundary⟩ := splitComponent_spec fs
  refine ⟨(splitComponent fs).1, (splitComponent fs).2, equal, unmarked, ?_⟩
  cases outer : (splitComponent fs).2 with
  | nil => exact Or.inl rfl
  | cons f tail => exact Or.inr ⟨f, tail, rfl, by simpa only [outer, Boundary] using boundary⟩

/-- Split a node's ancestor context at the boundary of its preferred component. -/
theorem split_component_context (fs : List Frame) :
    ∃ inner outer : List Frame, fs = inner ++ outer ∧
      (∀ f ∈ inner, f.marked = false) ∧ Boundary outer := by
  exact ⟨(splitComponent fs).1, (splitComponent fs).2, splitComponent_spec fs⟩

/-- A simulation of a whole auxiliary component can be transported through an
arbitrary enclosing reference context. Marked ancestors add neither rotations
nor amortized potential cost, regardless of the actual auxiliary shapes. -/
theorem simulate_boundary_context (fs : List Frame) (boundary : Boundary fs)
    (s child target : MarkedTree) (bound : ℝ)
    (same : s.nesting = (plug fs child).nesting) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      ∃ result : MarkedTree, ∃ cost : Nat,
        result.nesting = target.nesting ∧ Rotations actual.tree result.tree cost ∧
        (cost : ℝ) + result.potential - actual.potential ≤ bound) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (plug fs target).nesting ∧ Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤ bound := by
  cases fs with
  | nil => exact localUpdate s same
  | cons f fs =>
    obtain ⟨before, after, heq, unmarked, ending⟩ := split_marks fs
    have decomposed (t : MarkedTree) : plug (f :: fs) t = plug after (plug (f :: before) t) := by
      rw [heq, ← List.cons_append, plug_append]
    rcases ending with empty | ⟨g, tail, rest, marked⟩
    · have equal : fs = before := by simpa only [empty, List.append_nil] using heq
      rw [equal] at same ⊢
      exact simulate_boundary_segment s child target f boundary before unmarked bound same nonempty localUpdate
    · have source : s.nesting = (plug (g :: tail) (plug (f :: before) child)).nesting := by
        simpa only [decomposed, rest] using same
      have smaller : (g :: tail).length < (f :: fs).length := by
        have lengths := congrArg List.length heq
        simp only [List.length_append, rest, List.length_cons] at lengths ⊢
        omega
      have lifted := simulate_boundary_context (g :: tail) marked s
        (plug (f :: before) child) (plug (f :: before) target) bound source
        (plug_nonempty _ _ (by simp))
        (fun actual nested => simulate_boundary_segment actual child target f boundary
          before unmarked bound nested nonempty localUpdate)
      simpa only [decomposed, rest] using lifted
termination_by fs.length

end RotationBST.Tango.MarkedTree
