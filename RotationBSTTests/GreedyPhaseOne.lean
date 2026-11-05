module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.GreedyPhaseOne
open Geometric Geometric.GreedyASS Geometric.GreedyASS.Items
open Geometric.GreedyASS.Reference Geometric.GreedyASS.Potential
open Geometric.GreedyASS.Potential.PhaseOne

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def small : List Component := [⟨0, quad⟩, ⟨4, pair⟩, ⟨6, pair⟩]
private def large : List Component := [⟨0, quad⟩, ⟨4, quad⟩]
private def sample : Finset Point := Virgin.points [4, 5, 6]

private theorem small_cut : Transitions.Cut eight 0 small := by
  have step : Transitions.Step (forest eight 0 6) (.merge 6 .nil .nil) small := by
    change Transitions.Step [⟨0, quad⟩, ⟨4, pair⟩, ⟨6, .nil⟩, ⟨7, .nil⟩] _ small
    exact Transitions.Step.merge [⟨0, quad⟩, ⟨4, pair⟩] [] 6 .nil .nil
  exact step.cut ⟨2, .right (.right (.root pair 6))⟩ (Transitions.forest_cut eight 0 6)

private theorem merge_admissible : Transitions.Admissible eight 0 (.merge 4 pair pair) :=
  ⟨1, .right (.root quad 4)⟩
private theorem merge_step : Transitions.Step small (.merge 4 pair pair) large :=
  Transitions.Step.merge [⟨0, quad⟩] [] 4 pair pair
private theorem large_cut : Transitions.Cut eight 0 large := merge_step.cut merge_admissible small_cut

-- This is an actual intermediate merge, not a jump between search forests.
-- Three active items gain one each; absent columns still have zero amount.
example : totalAt eight 0 [4, 5, 6] sample small (Finset.range 8) = 9 ∧
    totalAt eight 0 [4, 5, 6] sample large (Finset.range 8) = 12 ∧
    chargedKeys eight 0 sample ⟨4, pair⟩ = {4, 5} ∧
    chargedKeys eight 0 sample ⟨6, pair⟩ = {6} ∧
    rootBlue small 5 = 3 ∧ rootBlue large 5 = 4 := by decide
example : totalAt eight 0 [4, 5, 6] sample large (Finset.range 8) ≤
    totalAt eight 0 [4, 5, 6] sample small (Finset.range 8) + 12 :=
  PhaseOne.Results.local_change eight 0 [4, 5, 6] (by decide) (by decide)
    small_cut merge_step merge_admissible (Finset.range 8)
example : (chargedKeys eight 0 sample ⟨4, pair⟩).card ≤ 6 :=
  PhaseOne.Results.charges (.right (.left (.root pair 4))) (by decide)

-- Reversing the same valid rewrite is a split and cannot increase potential.
example : totalAt eight 0 [4, 5, 6] sample small (Finset.range 8) ≤
    totalAt eight 0 [4, 5, 6] sample large (Finset.range 8) := by
  simpa only [Transitions.Event.isMerge, Bool.false_eq_true, ite_false, Nat.add_zero,
    small, List.append_nil, List.cons_append, List.nil_append,
    show 4 + leaves pair = 6 from by decide] using
    PhaseOne.Results.local_change eight 0 [4, 5, 6] (by decide) (by decide) large_cut
      (Transitions.Step.split [⟨0, quad⟩] [] 4 pair pair)
      (by exact ⟨1, .right (.root quad 4)⟩) (Finset.range 8)

-- A historical purple floor survives a decrease in current blue. Increasing
-- blue above the floor instead hits the fixed red cap; neither changes value.
example : RightGlancing (Virgin.points [3, 5, 4, 3]) (4, 2) ∧
    purple eight 0 [3, 5, 4, 3] 2 4 = 4 ∧
    select eight 0 [3, 5, 4, 3] (Virgin.points [3, 5, 4, 3]) (4, 2) 2 = WithTop.some 4 ∧
    select eight 0 [3, 5, 4, 3] (Virgin.points [3, 5, 4, 3]) (4, 2) 5 = WithTop.some 4 := by decide

-- Endpoint bridge theorems use the old point set throughout Phase I.
example : totalAt eight 0 [4, 5, 6] sample (forest eight 0 6) (Finset.range 8) =
    totalAmount eight 0 [4, 5, 6] sample (Finset.range 8) :=
  PhaseOne.Results.initial eight 0 [4, 5] 6 (n := 8) (by unfold History; decide) (by decide) _
example : totalAt eight 0 [4, 5, 6] sample (forest eight 0 0) (Finset.range 8) =
    totalAmount eight 0 [4, 5, 6, 0] sample (Finset.range 8) :=
  PhaseOne.Results.final eight 0 [4, 5, 6] 0 (n := 8) (by unfold History; decide) (by decide) _

-- The complete Phase-I theorem includes the virgin contribution and the
-- actual old/intermediate item potentials. Repeated searches have zero budget.
example : totalAmount eight 0 [4, 5, 6, 0] sample (Finset.range 8) + Virgin.before eight 0 [4, 5, 6] 0 ≤
    totalAmount eight 0 [4, 5, 6] sample (Finset.range 8) + Virgin.after eight 0 [4, 5] 6 +
      24 * Transitions.edges eight 0 6 0 :=
  PhaseOne.Results.step eight 0 [4, 5] 6 0 (by decide) _
example : totalAmount eight 0 [4, 5, 6, 6] sample (Finset.range 8) + Virgin.before eight 0 [4, 5, 6] 6 ≤
    totalAmount eight 0 [4, 5, 6] sample (Finset.range 8) + Virgin.after eight 0 [4, 5] 6 := by
  simpa only [show Transitions.edges eight 0 6 6 = 0 from by decide, Nat.mul_zero, Nat.add_zero,
    sample, List.cons_append, List.nil_append] using
    PhaseOne.Results.step eight 0 [4, 5] 6 6 (by decide) (Finset.range 8)

end RotationBST.Tests.GreedyPhaseOne
