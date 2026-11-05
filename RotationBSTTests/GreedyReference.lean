module

public import RotationBST.Algorithms.GreedyASS.Reference.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyReference
open Geometric Geometric.GreedyASS.Reference

private def pair : Tree := .node .nil .nil
private def four : Tree := .node pair pair
private def eight : Tree := .node four four
private def middle : Component := ⟨2, pair⟩

-- Nil is a reference leaf, not an empty key universe. Global offsets survive
-- the recursive construction, including equal-shaped sibling occurrences.
example : leaves eight = 8 ∧ eight.size = 7 := by decide
example : forest .nil 5 5 = [⟨5, .nil⟩] := by decide
example : forest eight 0 1 = [⟨0, .nil⟩, ⟨1, .nil⟩, middle, ⟨4, four⟩] := by decide
example : forest eight 10 11 = [⟨10, .nil⟩, ⟨11, .nil⟩, ⟨12, pair⟩, ⟨14, four⟩] := by decide

example : ∃! c, c ∈ forest eight 0 1 ∧ c.Contains 6 :=
  Results.partition eight 0 1 6 (by decide)

example : (0 < middle.first ∧ 1 < middle.first) ∨
    (middle.last ≤ 0 ∧ middle.last ≤ 1) :=
  Results.side eight 0 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

example : (∀ x ∈ [2, 3, 2], x < (Component.mk 0 pair).first) ∨
    (∀ x ∈ [2, 3, 2], (Component.mk 0 pair).last ≤ x) :=
  Results.stream four 0 2 [3, 2] (by decide) (by decide) (by decide)

-- The searched leaf survives. Hence forest membership alone cannot justify
-- the assertion that a search lies outside every component's interval.
example : (⟨0, .nil⟩ : Component) ∈ forest pair 0 0 ∧
    (⟨0, .nil⟩ : Component) ∈ forest pair 0 1 ∧
    (Component.mk 0 .nil).Contains 0 := by
  unfold Component.Contains
  decide

private def past : Finset Point := fill greedySweep 0 ∅ [7, 3, 1]
private theorem history : History 8 3 past := by unfold History; decide

-- The middle component was touched at key 3 by the search for key 1. While
-- it persists for searches 0 and 1, older key 7 cannot be accessed again.
example : (3, 2) ∈ past ∧ (7, 1) ∈ past := by decide
example : ∀ p ∈ fill greedySweep 3 past [0, 1, 0], 2 < p.2 → p.1 ≤ 3 := by
  have within : middle.Contains 3 := by unfold Component.Contains; decide
  rcases Results.access eight 0 1 [0, 1, 0] history (by decide) within
    (by decide) (by decide) (by decide) with left | right
  · exact left.2
  · exact False.elim ((by decide : ¬ middle.last ≤ 1) (right.1 1 (by simp)))

-- The stronger point-side formulation permits returning to the component's
-- own searched singleton. The singleton need not be excluded from the stream.
example : (∀ x ∈ [3, 2, 3], x ≤ 3) ∨ (∀ x ∈ [3, 2, 3], 3 ≤ x) := by
  have within : (Component.mk 3 .nil).Contains 3 := by unfold Component.Contains; decide
  exact Results.point_side eight 0 [3, 2, 3] within (by decide) (by decide)

example : ∀ p ∈ fill greedySweep 2 (fill greedySweep 0 ∅ [7, 3]) [3, 2, 3],
    1 < p.2 → p.1 ≤ 3 := by
  have hist : History 8 2 (fill greedySweep 0 ∅ [7, 3]) := by unfold History; decide
  have within : (Component.mk 3 .nil).Contains 3 := by unfold Component.Contains; decide
  rcases Results.barrier eight 0 [3, 2, 3] hist (by decide) within
    (by decide) (by decide) with left | right
  · exact left.2
  · exact False.elim ((by decide : ¬ 3 ≤ 2) (right.1 2 (by simp)))

end RotationBST.Tests.GreedyReference
