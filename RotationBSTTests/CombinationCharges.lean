module

public import RotationBST.Algorithms.GreedyASS.Combination.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.CombinationCharges
open Combo

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node leaf leaf

-- The middle repeated-key window costs two in the original execution but
-- three when restarted at the root. A proof omitting initialization would
-- incorrectly assert a bound of two for this standalone segment.
example : Analysis.mass (fun _ => Charges.lazyFinger 1 balanced) false [0, 0, 0] 1 3 = 2 ∧
    Analysis.total (fun _ => Charges.lazyFinger 1 balanced) false
      (Analysis.segment [0, 0, 0] 1 3) = 3 := by
  rw [Charges.Results.lazyFinger_mass _ _ _ _ _ _ (by omega), Charges.Results.lazyFinger_total]
  norm_num [Analysis.segment, LazyFinger.cost, LazyFinger.costFrom, LazyFinger.distance,
    Tree.depth, balanced, leaf, Tree.size]

-- A segment of length zero incurs no charges, even at the end of a sequence.
example : Analysis.mass (fun _ => Charges.lazyFinger 46225920 balanced) true [0, 2] 2 2 = 0 := by
  simp [Analysis.mass]

-- The same worker serves both reference trees: no comparator is an input to
-- the planner's choice. This is the quantifier order needed by Theorem 4.3.
example : ∃ p : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) (.node leaf .nil),
    Analysis.WellBehaved (Worker.Replay.worker p) 2 (46225920 * 2) 1 20
      (fun _ => Charges.lazyFinger 46225920 (.node leaf .nil)) ∧
    Analysis.WellBehaved (Worker.Replay.worker p) 2 (46225920 * 2) 1 20
      (fun _ => Charges.lazyFinger 46225920 (.node .nil leaf)) := by
  obtain ⟨p, all⟩ := Geometric.GreedyASS.Combination.Results.greedy_worker (.node leaf .nil)
  exact ⟨p, all _ rfl, all _ rfl⟩

-- The empty universe supports exactly the empty valid request sequence; the
-- uniform contract does not assume a nonexistent initial key.
example : ∃ p : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) .nil,
    Analysis.WellBehaved (Worker.Replay.worker p) 0 0 1 20
      (fun _ => Charges.lazyFinger 46225920 .nil) := by
  obtain ⟨p, all⟩ := Geometric.GreedyASS.Combination.Results.greedy_worker .nil
  exact ⟨p, all _ rfl⟩

end RotationBST.Tests.CombinationCharges
