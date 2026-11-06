module

public import RotationBST.Algorithms.Deamortization.Algorithm.Definitions.Abstract
public import RotationBST.Algorithms.Deamortization.Replay.Abstract
public import RotationBST.Algorithms.Combination.Worker.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Algorithm

/-- Instantiate abstract deamortization for any certified rotation algorithm,
retaining a single physical program before every future cost comparison. -/
theorem implementation_exists (source : RotationBST.Algorithm) (saved : Tree) (nonempty : saved ≠ .nil) :
    Nonempty (Implementation source saved) := by
  obtain ⟨planner, _, bound⟩ := Combo.Worker.Replay.Results.algorithm_planner (fun _ => source) saved
  obtain ⟨initial, startup, program, trace, setup, correct, causal⟩ := Replay.Results.deamortize planner false nonempty
  refine ⟨⟨initial, startup, program, trace, setup, ?_, causal⟩⟩
  intro keys valid
  obtain ⟨out, completed, replay, served, execution, length, total, cost, worst⟩ := correct keys valid
  have sourceBound := bound false keys valid
  exact ⟨out, completed, replay, served, execution, length, total, by omega, worst⟩

theorem Implementation.total_bound {source : RotationBST.Algorithm} {saved : Tree}
    (d : Implementation source saved) {keys : List Nat} (valid : ∀ x ∈ keys, x < saved.size)
    {out : Scheduler.Output} (completed : d.program keys = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 79360 * source.totalCost saved keys := by
  obtain ⟨result, finished, _, _, _, _, _, bound, _⟩ := d.correct keys valid
  have same := Option.some.inj (completed.symm.trans finished)
  subst result
  have setup := d.setup_bound
  omega

/-- Every source bound transfers to the already chosen program; choosing a
benchmark does not select another execution or initial representation. -/
theorem Implementation.transfer {source : RotationBST.Algorithm} {saved : Tree}
    (d : Implementation source saved) {keys : List Nat} (valid : ∀ x ∈ keys, x < saved.size)
    {out : Scheduler.Output} (completed : d.program keys = some out) {bound : ℝ}
    (sourceBound : (source.totalCost saved keys : ℝ) ≤ bound) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 79360 * bound := by
  have total : (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 79360 * (source.totalCost saved keys : ℝ) := by
    exact_mod_cast d.total_bound valid completed
  linarith

/-- Dynamic optimality, if available for a source, survives the abstract
worst-case transformation with constants uniform over all starting trees.
The output witnesses include physical service, causality and per-search bounds. -/
theorem dynamic_optimal (source : RotationBST.Algorithm) (optimal : TotallyDynamicallyOptimal source) :
    ∃ C D : Nat, ∀ saved : Tree, saved ≠ .nil →
      ∃ d : Implementation source saved, ∀ (xs : List Nat) (finish : Tree) (k : Nat),
        RotationBST.Execution saved xs finish k → ∀ out,
          d.program xs = some out → d.startup + out.costs.sum ≤ C * (xs.length + k) + D * saved.size := by
  obtain ⟨C, D, bound⟩ := optimal
  refine ⟨79360 * C, 16 + 79360 * D, ?_⟩
  intro saved nonempty
  obtain ⟨d⟩ := implementation_exists source saved nonempty
  refine ⟨d, ?_⟩
  intro xs finish k execution out completed
  have sourceBound := bound saved xs finish k execution
  have total := d.total_bound (AccessBridge.execution_valid execution) completed
  nlinarith

end RotationBST.Deamortization.Algorithm
