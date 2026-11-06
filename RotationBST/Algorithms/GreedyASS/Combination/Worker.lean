module

public import RotationBST.Algorithms.GreedyASS.Performance.Abstract
public import RotationBST.Algorithms.Combination.Charges.Abstract
public import RotationBST.Algorithms.Combination.Worker.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination
open Combo

/-- One causal GreedyASS worker satisfies the combination hypotheses against
all fixed reference trees simultaneously. The planner is chosen before the
reference tree, request sequence, and segment; initialization is linear.
This supplies the GreedyASS input to Theorem 4.3, not its Tango input or the
final deamortized combination. -/
theorem greedy_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      ∀ t : Tree, t.size = saved.size →
        Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
          (46225920 * saved.size) 1 20 (fun _ => Charges.lazyFinger 46225920 t) := by
  obtain ⟨a, source⟩ := Performance.Results.bst saved.size
  obtain ⟨planner, inherit⟩ := Worker.Replay.Results.algorithms_well_behaved (fun _ => a) saved
  refine ⟨planner, ?_⟩
  intro t size
  apply inherit (46225920 * saved.size) 1 20 (fun _ => Charges.lazyFinger 46225920 t)
    (by omega) (by decide +kernel)
  · intro side xs i
    exact Charges.lazyFinger_nonneg _ _ _ _
  · intro side xs valid
    have bound := (source saved rfl xs valid).1
    have optimal := LazyFinger.Results.optimal_le t xs
    rw [size] at optimal
    rw [Charges.lazyFinger_total]
    have upper : 64 * a.totalCost saved xs ≤ 46225920 * LazyFinger.cost t xs + 46225920 * saved.size := by omega
    exact_mod_cast upper
  · intro side xs valid lo hi ordered _inside
    have stable := Charges.lazyFinger_stable 46225920 (46225920 * saved.size) t side xs lo hi ordered
      (by simpa only [size] using valid) (by rw [size])
    norm_num only [Nat.cast_one, one_mul, Nat.cast_mul, Nat.cast_ofNat] at stable ⊢
    nlinarith [Nat.cast_nonneg saved.size (α := ℝ)]

end RotationBST.Geometric.GreedyASS.Combination
