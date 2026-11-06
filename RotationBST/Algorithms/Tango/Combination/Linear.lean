module

public import RotationBST.Algorithms.Tango.Combination.Worker
public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Linear
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Combination
open Combo

theorem linear_factor_lower (reference : Tree) :
    64 * (17 * Real.logb 2 (height reference) + 6) ≤ (linearChargeFactor reference : ℝ) := by
  have previous := factor_lower reference
  have nonnegative := Bounds.logb_nat_nonneg (height reference)
  simp only [linearChargeFactor, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem balanced_linear_factor (n : Nat) : linearChargeFactor (balanced n) ≤
    2 * ⌈64 * (14 * Real.logb 2 (Nat.log2 n + 1) + 6)⌉₊ :=
  Nat.mul_le_mul_left 2 (balanced_factor n)

/-- The bottom-up source supplies an interruptible worker with linear restart
allowance, uniformly over every request sequence and comparison segment. -/
theorem linear_balanced_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (2816 * saved.size) 1 20
        (fun _ => Charges.interleave (linearChargeFactor (balanced saved.size)) (balanced saved.size)) := by
  let reference := balanced saved.size
  let p := BottomUp.policy reference
  have same : saved.size = reference.size := (balanced_size saved.size).symm
  obtain ⟨a, _exactRun, source⟩ := p.rotation_algorithm
  obtain ⟨planner, inherit⟩ := Worker.Replay.Results.algorithms_well_behaved (fun _ => a) saved
  refine ⟨planner, ?_⟩
  apply inherit (2816 * saved.size) 1 20
    (fun _ => Charges.interleave (linearChargeFactor reference) reference)
  · omega
  · decide +kernel
  · intro side xs i
    exact Charges.interleave_nonneg _ _ _ _
  · intro side xs valid
    have keys : ∀ x ∈ xs, x < reference.size := by simpa only [same] using valid
    have sourceBound := source saved same xs keys
    have tango := BottomUp.linear_run_bound p (fun _ _ _ => rfl) xs keys
    have startup := Initialization.balanced_localAllowance saved.size
    have cost : (a.totalCost saved xs : ℝ) ≤ xs.length + (p.run xs).2 + 2 * saved.size := by exact_mod_cast sourceBound
    have nonnegative := Bounds.logb_nat_nonneg (height reference)
    have factorBound := mul_le_mul_of_nonneg_right (linear_factor_lower reference)
      (show (0 : ℝ) ≤ Wilber.interleave reference xs + xs.length by positivity)
    rw [Charges.interleave_total]
    push_cast
    change Initialization.localAllowance reference ≤ 42 * saved.size at startup
    nlinarith [mul_nonneg nonnegative (Nat.cast_nonneg (Wilber.interleave reference xs) : (0 : ℝ) ≤ Wilber.interleave reference xs)]
  · intro side xs _valid lo hi ordered _inside
    have stable := Charges.interleave_stable (linearChargeFactor reference) reference side xs lo hi ordered
    norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (2816 * saved.size) (α := ℝ)]

end RotationBST.Tango.Combination
