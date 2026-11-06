module

public import RotationBST.Algorithms.GreedyASS.Combination.Deamortized.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Combination.Abstract
public import RotationBST.Algorithms.Deamortization.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination
open Combo

/-- The same combined policy now has logarithmic worst-case response costs,
with constant-factor total overhead and a separate linear setup trace. -/
theorem deamortized_exists {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (nonempty : saved ≠ .nil) : Nonempty (Deamortized p) := by
  obtain ⟨initial, startup, program, trace, setup, correct, causal⟩ :=
    Deamortization.Replay.Results.deamortize p.implementation.planner false nonempty
  refine ⟨⟨initial, startup, program, trace, setup, ?_, causal⟩⟩
  intro keys valid
  obtain ⟨out, completed, replay, served, execution, length, total, bound, worst⟩ := correct keys valid
  have source := (Online.Replay.Results.run_bound p.prepared p.implementation false none keys valid).2
  rw [p.implementation.initial] at bound
  dsimp only at bound
  change _ ≤ 2 * p.cost keys at source
  refine ⟨out, completed, replay, served, execution, length, total, ?_, worst⟩
  omega

/-- The total bound counts both setup and the exact emitted response costs. -/
theorem Deamortized.total_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) {keys : List Nat}
    (valid : ∀ x ∈ keys, x < saved.size) {out : Deamortization.Scheduler.Output}
    (completed : d.program keys = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 2480 * p.cost keys := by
  obtain ⟨result, finished, _, _, _, _, _, bound, _⟩ := d.correct keys valid
  have same := Option.some.inj (completed.symm.trans finished)
  subst result
  have setup := d.setup_bound
  omega

/-- All weight infima and offline executions compare against one already
chosen deamortized program. Its shared startup allowance is linear. -/
theorem Deamortized.weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
        3839872 * overhead saved) := by
  have valid : ∀ x ∈ xs, x < saved.size := by
    rw [← size]
    exact AccessBridge.execution_valid execution
  have total : (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 * (p.cost xs : ℝ) := by
    exact_mod_cast d.total_bound valid completed
  have bound := Results.weighted_competitive p start key size execution
  linarith

/-- Every positive weighting satisfies the same bound for that fixed program. -/
theorem Deamortized.weights_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) (start : Nat) (key : start < saved.size)
    (w : Nat → ℝ) (positive : ∀ x < saved.size, 0 < w x)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.costFrom w start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
        3839872 * overhead saved) := by
  have valid : ∀ x ∈ xs, x < saved.size := by
    rw [← size]
    exact AccessBridge.execution_valid execution
  have total : (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 * (p.cost xs : ℝ) := by
    exact_mod_cast d.total_bound valid completed
  have bound := Results.weights_competitive p start key w positive size execution
  linarith

end RotationBST.Geometric.GreedyASS.Combination
