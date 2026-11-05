module

public import RotationBST.Algorithms.GreedyASS.Virgin.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.GreedyVirginTransitions
open Geometric Geometric.GreedyASS.Reference Geometric.GreedyASS.Virgin

private def pair : Tree := .node .nil .nil
private def four : Tree := .node pair pair

-- Searching the sibling leaves changes no endpoint component. The used
-- singleton remains non-virgin, even though the conceptual plan merges and
-- then splits its parent.
private theorem used : NonVirgin four 0 [0] 0 ⟨0, .nil⟩ := by
  have lifetime := Results.lifetime four 0 [] 0 0 (⟨0, .nil⟩ : Component)
  simp only [List.nil_append] at lifetime
  rw [lifetime]
  refine ⟨by decide, Or.inr ⟨by decide, 0, by decide, by decide⟩⟩
example : NonVirgin four 0 [0] 1 ⟨0, .nil⟩ :=
  (Results.survival four 0 [] 0 1 (by decide) (by decide)).mpr used

-- A zero-event trace is also a valid witness for the equal endpoint
-- forests. It proves that virgin potential does not increase at all.
example : before four 0 [0] 1 ≤ after four 0 [] 0 := by
  have same : forest four 0 0 = forest four 0 1 := by decide
  have trace : Transitions.Trace (forest four 0 0) [] (forest four 0 1) := by
    rw [← same]
    exact .nil _
  simpa only [List.nil_append, Transitions.introductions, List.map_nil, List.sum_nil,
    Nat.mul_zero, Nat.add_zero] using Results.transition four 0 [] 0 1 trace

-- Root-introduction budgets apply to actual histories and both directions
-- of an unequal-depth reference path, without assuming any item bound.
example : before (.node .nil pair) 10 [10] 12 + 12 ≤
    after (.node .nil pair) 10 [] 10 + 72 := by
  simpa only [List.nil_append, show Transitions.merges (Transitions.plan (.node .nil pair) 10 10 12) = 1 from by decide,
    show Transitions.edges (.node .nil pair) 10 10 12 = 3 from by decide] using
    Results.phase_one_budget (.node .nil pair) 10 [] 10 12
example : before (.node .nil pair) 10 [12] 10 + 24 ≤
    after (.node .nil pair) 10 [] 12 + 72 := by
  simpa only [List.nil_append, show Transitions.merges (Transitions.plan (.node .nil pair) 10 12 10) = 2 from by decide,
    show Transitions.edges (.node .nil pair) 10 12 10 = 3 from by decide] using
    Results.phase_one_budget (.node .nil pair) 10 [] 12 10
example : before four 0 [0, 3, 2] 0 ≤ after four 0 [0, 3] 2 +
    12 * Transitions.introductions (Transitions.plan four 0 2 0) :=
  Results.forest_change four 0 [0, 3] 2 0

end RotationBST.Tests.GreedyVirginTransitions
