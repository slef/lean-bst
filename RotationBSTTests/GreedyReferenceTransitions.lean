module

public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.GreedyReferenceTransitions
open Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Reference.Transitions

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad

-- A repeated search changes nothing. Distinct sibling leaves share a forest,
-- but the prescribed LCA route still has one merge and one split.
example : plan eight 0 3 3 = [] := Results.repeated eight 0 3
example : forest eight 0 0 = forest eight 0 1 ∧
    plan eight 0 0 1 = [.merge 0 .nil .nil, .split 0 .nil .nil] := by decide

-- Crossing the root has six events, with all merges before all splits.
example : plan eight 0 0 7 =
    [.merge 0 .nil .nil, .merge 0 pair pair, .merge 0 quad quad,
      .split 0 quad quad, .split 4 pair pair, .split 6 .nil .nil] := by decide
example : Trace (forest eight 0 0) (plan eight 0 0 7) (forest eight 0 7) :=
  (Results.transition eight 0 0 7).1

-- A shallower LCA leaves the entire right half untouched, including at the
-- boundary between the merge and split phases.
private theorem merge_trace : Trace (forest eight 0 0)
    [.merge 0 .nil .nil, .merge 0 pair pair] [⟨0, quad⟩, ⟨4, quad⟩] :=
  .cons (Step.merge [] [⟨2, pair⟩, ⟨4, quad⟩] 0 .nil .nil)
    (.cons (Step.merge [] [⟨4, quad⟩] 0 pair pair) (.nil _))

private theorem middle_cut : Cut eight 0 [⟨0, quad⟩, ⟨4, quad⟩] :=
  plan_prefix_cut eight 0 0 3
    (remaining := [.split 0 pair pair, .split 2 .nil .nil]) (by decide) merge_trace

example : ∃! c, c ∈ [Component.mk 0 quad, Component.mk 4 quad] ∧ c.Contains 3 :=
  Results.ownership middle_cut (by decide)

example : ∃ roots,
    Trace (forest eight 0 0) [.merge 0 .nil .nil, .merge 0 pair pair] roots ∧
      Trace roots [.split 0 pair pair, .split 2 .nil .nil] (forest eight 0 3) ∧
      Cut eight 0 roots :=
  Results.intermediate eight 0 0 3 _ _ (by decide)

-- Translated, unequal-depth leaves have a three-edge path. Node-counted
-- upward paths sum to five, retaining both copies of the LCA.
example : (plan (.node .nil pair) 10 10 12).length = 3 ∧
    Distance.toRoot (Distance.lca (.node .nil pair) 10 10 12) 10 +
      Distance.toRoot (Distance.lca (.node .nil pair) 10 10 12) 12 = 5 := by decide
example : (plan (.node .nil pair) 10 10 12).length + 2 =
    Distance.toRoot (Distance.lca (.node .nil pair) 10 10 12) 10 +
      Distance.toRoot (Distance.lca (.node .nil pair) 10 10 12) 12 :=
  Results.path _ _ _ _ (by decide) (by decide)

-- A split changes an affected leaf's root distance by one. A component
-- outside the split retains its distance.
example : Distance.toRoot ⟨0, pair⟩ 1 ≤ Distance.toRoot ⟨0, quad⟩ 1 ∧
    Distance.toRoot ⟨0, quad⟩ 1 ≤ Distance.toRoot ⟨0, pair⟩ 1 + 1 :=
  Results.local_distance (Step.split [] [⟨4, quad⟩] 0 pair pair) middle_cut.ordered
    (by simp [quad]) (by simp) (by decide) (by decide)
example : Distance.toRoot ⟨4, quad⟩ 6 ≤ Distance.toRoot ⟨4, quad⟩ 6 ∧
    Distance.toRoot ⟨4, quad⟩ 6 ≤ Distance.toRoot ⟨4, quad⟩ 6 + 1 :=
  Results.local_distance (Step.split [] [⟨4, quad⟩] 0 pair pair) middle_cut.ordered
    (by simp) (by simp) (by decide) (by decide)

-- Adjacent leaves need not be siblings. A syntactic merge exists here, but
-- its parent is absent from this right-comb reference tree.
example : Step [⟨0, .nil⟩, ⟨1, .nil⟩, ⟨2, pair⟩] (.merge 0 .nil .nil)
    [⟨0, pair⟩, ⟨2, pair⟩] := Step.merge [] [⟨2, pair⟩] 0 .nil .nil
example : ¬ Admissible (.node .nil (.node .nil pair)) 0 (.merge 0 .nil .nil) := by
  rintro ⟨k, occurrence⟩
  change Distance.Occurs (.node .nil (.node .nil pair)) 0 ⟨0, pair⟩ k at occurrence
  cases occurrence with
  | left h => cases h
  | right h =>
    have bounds := h.bounds
    simp [leaves] at bounds

-- Root births count the actual local events, even if the endpoint forests
-- agree. A sibling-to-sibling path has one temporary merge and one split.
example : introductions (plan eight 0 0 1) = 3 ∧ merges (plan eight 0 0 1) = 1 ∧
    ((forest eight 0 1).toFinset \ (forest eight 0 0).toFinset).card = 0 := by decide
example : ((forest eight 0 7).toFinset \ (forest eight 0 0).toFinset).card ≤
    introductions (plan eight 0 0 7) :=
  Results.new_roots (Results.transition eight 0 0 7).1
example : introductions (plan eight 0 0 7) = 9 ∧ merges (plan eight 0 0 7) = 3 := by decide

-- Unequal-depth paths have different birth counts in the two directions,
-- but births plus merge allowance always equal twice the edge count.
example : introductions (plan (.node .nil pair) 10 10 12) = 5 ∧
    merges (plan (.node .nil pair) 10 10 12) = 1 ∧
    introductions (plan (.node .nil pair) 10 12 10) = 4 ∧
    merges (plan (.node .nil pair) 10 12 10) = 2 := by decide
example : introductions (plan (.node .nil pair) 10 10 12) +
    merges (plan (.node .nil pair) 10 10 12) = 2 * (plan (.node .nil pair) 10 10 12).length :=
  Results.birth_budget _
example : introductions (plan eight 0 3 3) = 0 ∧ merges (plan eight 0 3 3) = 0 := by decide

end RotationBST.Tests.GreedyReferenceTransitions
