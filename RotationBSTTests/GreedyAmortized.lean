module

public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyAmortized
open Geometric Geometric.GreedyASS Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential Geometric.GreedyASS.Potential.Amortized

private def pair : Tree := .node .nil .nil
private def balanced : Tree := .node pair pair
private def skew : Tree := .node .nil (.node .nil pair)

-- The benchmark counts actual leaf-to-leaf edges, rather than two root
-- traversals. Repeated requests cost one and the first has no predecessor.
example : referenceCost skew 0 [0, 3, 0, 3] = 16 ∧
    referenceCost balanced 0 [0, 3, 0, 3] = 16 ∧
    referenceCost skew 0 [2, 3, 2, 3] = 10 ∧
    referenceCost skew 0 [3, 3, 3] = 3 ∧
    rowCost greedySweep 0 ∅ [0, 3, 0, 3] = 6 := by decide
example : Virgin.keys [0] 3 = {0, 3} ∧ Virgin.keys [0, 3] 0 = {0} ∧
    Virgin.keys [0, 3, 0] 3 = {0, 3} := by decide

-- Empty streams, singleton universes, and repeated searches are all
-- covered by the public whole-stream theorem.
example : rowCost greedySweep 0 ∅ [] ≤ 24 * referenceCost skew 0 [] + 15 * leaves skew :=
  Results.cost skew 0 [] (by simp)
example : rowCost greedySweep 0 ∅ [0, 0, 0] ≤ 24 * referenceCost .nil 0 [0, 0, 0] + 15 :=
  Results.cost .nil 0 [0, 0, 0] (by decide)
example : rowCost greedySweep 0 ∅ [0, 3, 0, 3] ≤ 24 * 16 + 15 * 4 := by
  simpa only [show referenceCost skew 0 [0, 3, 0, 3] = 16 from by decide,
    show leaves skew = 4 from by decide] using Results.cost skew 0 [0, 3, 0, 3] (by decide)

-- Translating all ranks does not inflate the startup allowance: it is
-- fifteen per leaf, not fifteen times the largest rank.
example : rowCost greedySweep 0 ∅ [10, 13, 10, 13] = 6 ∧
    referenceCost skew 10 [10, 13, 10, 13] = 16 := by decide
example : rowCost greedySweep 0 ∅ [10, 13, 10, 13] ≤ 24 * 16 + 15 * 4 := by
  simpa only [show referenceCost skew 10 [10, 13, 10, 13] = 16 from by decide,
    show leaves skew = 4 from by decide] using Results.cost skew 10 [10, 13, 10, 13] (by decide)

-- Telescoping retains final potential and counts only two encountered
-- columns even though the stream contains four requests.
example : ((Virgin.points [0, 3, 0, 3]).image Prod.fst).card = 2 := by decide
example : (Virgin.points [0, 3, 0, 3]).card + potential skew 0 [0, 3, 0, 3] ≤
    12 * leaves skew + 24 * referenceCost skew 0 [0, 3, 0, 3] + 3 * 2 := by
  simpa only [show ((Virgin.points [0, 3, 0, 3]).image Prod.fst).card = 2 from by decide] using
    Results.stream skew 0 [0, 3, 0, 3] (by decide)

-- A single causal BST policy supports two different references on every
-- valid stream; the reference is not an input to policy selection.
example : ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = 4 →
    ∀ xs : List Nat, (∀ x ∈ xs, x < 4) →
      algorithm.totalCost initial xs ≤ 144456 * referenceCost balanced 0 xs + 96303 * 4 ∧
      algorithm.totalCost initial xs ≤ 144456 * referenceCost skew 0 xs + 96303 * 4 := by
  obtain ⟨algorithm, bound⟩ := Results.bst 4
  exact ⟨algorithm, fun initial size xs valid =>
    ⟨bound initial size balanced (by decide) xs valid, bound initial size skew (by decide) xs valid⟩⟩

end RotationBST.Tests.GreedyAmortized
