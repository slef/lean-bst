module

public import RotationBST.Algorithms.GreedyASS.Combination.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Combination.Worker
public import RotationBST.Algorithms.Tango.Combination.Abstract
public import RotationBST.Algorithms.Combination.Analysis.Monotone
public import RotationBST.Algorithms.Combination.Worker.Pair.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination
open Combo

theorem size_le_overhead (saved : Tree) : saved.size ≤ overhead saved := by
  unfold overhead
  omega

/-- Choose the source workers once, uniformly over all lazy-finger references.
Only their proof-side charges vary with the reference tree. -/
theorem paired_inputs (saved : Tree) :
    ∃ left right : Worker.Replay.Planner SourceState saved,
      ∀ reference : Tree, reference.size = saved.size →
        Analysis.WellBehaved (Worker.Pair.worker (Worker.Replay.worker left) (Worker.Replay.worker right) false false)
          saved.size (overhead saved) 1 20 (charges saved reference) := by
  obtain ⟨left, leftWell⟩ := greedy_worker saved
  obtain ⟨right, rightWell⟩ := Tango.Combination.Results.linear_balanced_worker saved
  refine ⟨left, right, ?_⟩
  intro reference same
  have leftLarger : 46225920 * saved.size ≤ overhead saved := le_rfl
  have rightLarger : 2816 * saved.size ≤ overhead saved := by unfold overhead; omega
  have paired := Worker.Pair.Results.well_behaved
    ((leftWell reference same).overhead_mono leftLarger (by decide +kernel))
    (rightWell.overhead_mono rightLarger (by decide +kernel)) false false
  exact paired

end RotationBST.Geometric.GreedyASS.Combination
