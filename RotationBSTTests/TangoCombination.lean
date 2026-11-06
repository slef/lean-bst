module

public import RotationBST.Algorithms.Tango.Combination.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TangoCombination
open Combo

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node leaf leaf
private def vine : Tree := .node (.node leaf .nil) .nil

-- The executable source makes four rotations and returns to the balanced
-- shape. Its causal lift preserves both facts, including the private marks
-- reconstructed after the first two accesses. A different starting shape
-- pays at most six additional rotations, once for the entire sequence.
example : ∃ a : Algorithm,
    a.runFrom [] balanced [0, 2, 1] = (balanced, 4) ∧
    a.totalCost vine [0, 2, 1] ≤ 13 := by
  obtain ⟨a, exactRun, upper⟩ := Tango.Algorithm.Rotation.Results.rotation_algorithm (Tango.policy balanced)
  have valid : ∀ x ∈ [0, 2, 1], x < balanced.size := by
    intro x member
    change x < 3
    simp at member
    omega
  have computed : (((Tango.policy balanced).run [0, 2, 1]).1.tree,
      ((Tango.policy balanced).run [0, 2, 1]).2) = (balanced, 4) := by decide +kernel
  refine ⟨a, (exactRun _ valid).trans computed, ?_⟩
  have cost := congrArg Prod.snd computed
  have bound := upper vine rfl [0, 2, 1] valid
  rw [cost] at bound
  exact bound

-- A boundary switch belongs to the original window's charges; the restarted
-- segment omits it. The inequality can be strict without any startup term.
example : Analysis.mass (fun _ => Charges.interleave 1 balanced) false [0, 2, 0, 2] 1 3 = 4 ∧
    Analysis.total (fun _ => Charges.interleave 1 balanced) false [2, 0] = 3 := by
  rw [Charges.Results.interleave_mass _ _ _ _ _ _ (by omega), Charges.Results.interleave_total]
  norm_num [Wilber.interleave, Wilber.regions, Wilber.alternations, Wilber.leftRequests,
    Wilber.rightRequests, balanced, leaf, Tree.size]

-- Repeated requests still have a unit charge despite zero interleave switches.
example : Analysis.total (fun _ => Charges.interleave 1 balanced) true [1, 1, 1] = 3 := by
  rw [Charges.Results.interleave_total]
  norm_num [Wilber.interleave, Wilber.regions, Wilber.alternations, Wilber.leftRequests,
    Wilber.rightRequests, balanced, leaf, Tree.size]

example : Tango.Combination.chargeFactor balanced = 1280 := by
  norm_num [Tango.Combination.chargeFactor, Tango.height, balanced, leaf]

-- Empty universes remain valid: no artificial positivity hypothesis or
-- nonempty initial access is introduced by the adapter.
example : ∃ p : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) .nil,
    Analysis.WellBehaved (Worker.Replay.worker p) 0 0 1 20
      (fun _ => Charges.interleave (Tango.Combination.chargeFactor .nil) .nil) := by
  simpa only [Tree.size, Tango.balanced, Nat.mul_zero] using Tango.Combination.Results.balanced_worker .nil

-- The sharper worker also supports an empty universe, with zero startup.
example : ∃ p : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) .nil,
    Analysis.WellBehaved (Worker.Replay.worker p) 0 0 1 20
      (fun _ => Charges.interleave (Tango.Combination.linearChargeFactor .nil) .nil) := by
  simpa only [Tree.size, Tango.balanced, Nat.mul_zero] using Tango.Combination.Results.linear_balanced_worker .nil

end RotationBST.Tests.TangoCombination
