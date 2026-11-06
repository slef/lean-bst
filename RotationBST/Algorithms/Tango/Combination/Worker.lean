module

public import RotationBST.Algorithms.Tango.Combination.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Rotation.Abstract
public import RotationBST.Algorithms.Tango.Algorithm.Balanced
public import RotationBST.Algorithms.Combination.Worker.Replay.Abstract
public import RotationBST.Algorithms.Combination.Charges.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Combination
open Combo

theorem factor_lower (reference : Tree) :
    64 * (14 * Real.logb 2 (height reference) + 6) ≤ (chargeFactor reference : ℝ) := by
  exact Nat.le_ceil _

theorem factor_pos (reference : Tree) : 0 < chargeFactor reference := by
  have bound := factor_lower reference
  have nonneg := Bounds.logb_nat_nonneg (height reference)
  have positive : (0 : ℝ) < chargeFactor reference := by nlinarith
  exact_mod_cast positive

theorem balanced_factor (n : Nat) : chargeFactor (balanced n) ≤
    ⌈64 * (14 * Real.logb 2 (Nat.log2 n + 1) + 6)⌉₊ := by
  apply Nat.ceil_mono
  have monotone := Splay.Updates.log_nat_mono (balanced_height n)
  norm_num only [Nat.cast_add, Nat.cast_one] at monotone
  nlinarith

/-- A causal interruptible realization of Tango with a stable Wilber charge
for every contiguous segment. The initialization allowance retains the
height-dependent factor from the existing Tango theorem. -/
theorem worker {reference : Tree} (p : Policy reference) (saved : Tree) (same : saved.size = reference.size) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor reference * saved.size) 1 20 (fun _ => Charges.interleave (chargeFactor reference) reference) := by
  obtain ⟨a, _exactRun, source⟩ := p.rotation_algorithm
  obtain ⟨planner, inherit⟩ := Worker.Replay.Results.algorithms_well_behaved (fun _ => a) saved
  refine ⟨planner, ?_⟩
  apply inherit (chargeFactor reference * saved.size) 1 20
    (fun _ => Charges.interleave (chargeFactor reference) reference)
  · have positive := factor_pos reference
    nlinarith
  · decide +kernel
  · intro side xs i
    exact Charges.interleave_nonneg _ _ _ _
  · intro side xs valid
    have keys : ∀ x ∈ xs, x < reference.size := by simpa only [same] using valid
    have sourceBound := source saved same xs keys
    have tango := p.interleave_bound xs keys
    have cost : (a.totalCost saved xs : ℝ) ≤ xs.length + (p.run xs).2 + 2 * saved.size := by exact_mod_cast sourceBound
    have logNonneg := Bounds.logb_nat_nonneg (height reference)
    have factorBound := mul_le_mul_of_nonneg_right (factor_lower reference)
      (show (0 : ℝ) ≤ Wilber.interleave reference xs + xs.length + saved.size by positivity)
    rw [Charges.interleave_total]
    push_cast
    rw [← same] at tango
    nlinarith [mul_nonneg logNonneg (Nat.cast_nonneg xs.length : (0 : ℝ) ≤ xs.length)]
  · intro side xs _valid lo hi ordered _inside
    have stable := Charges.interleave_stable (chargeFactor reference) reference side xs lo hi ordered
    norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
    nlinarith [Nat.cast_nonneg (chargeFactor reference * saved.size) (α := ℝ)]

/-- The worker's actual execution compares with every offline execution using
one fixed worker, including arbitrary saved and comparator starting shapes. -/
theorem competitive_worker {reference : Tree} (p : Policy reference) (saved : Tree) (same : saved.size = reference.size) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor reference * saved.size) 1 20 (fun _ => Charges.interleave (chargeFactor reference) reference) ∧
      ∀ (s t : Tree) (xs : List Nat) (k : Nat), s.size = reference.size →
        RotationBST.Execution s xs t k → ∀ side,
          ∃ final cost, Worker.Requests (Worker.Replay.worker planner) side
            ((Worker.Replay.worker planner).restart side) xs final cost ∧
            (cost : ℝ) ≤ (4 * chargeFactor reference : Nat) * (xs.length + k : Nat) +
              (chargeFactor reference * saved.size : Nat) := by
  obtain ⟨planner, well⟩ := worker p saved same
  refine ⟨planner, well, ?_⟩
  intro s t xs k size execution side
  have valid : ∀ x ∈ xs, x < saved.size := by
    rw [same, ← size]
    exact AccessBridge.execution_valid execution
  obtain ⟨final, cost, ran, bound⟩ := well.upper side xs valid
  have compared := Charges.interleave_comparator (chargeFactor reference) reference size.symm execution
  change Analysis.total (fun _ => Charges.interleave (chargeFactor reference) reference) side xs ≤ _ at compared
  exact ⟨final, cost, ran, by linarith⟩

/-- Concrete balanced Tango supplies the interface for every universe size;
the input algorithm is the executable preferred-path policy. -/
theorem balanced_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor (balanced saved.size) * saved.size) 1 20
        (fun _ => Charges.interleave (chargeFactor (balanced saved.size)) (balanced saved.size)) :=
  worker (policy (balanced saved.size)) saved (balanced_size saved.size).symm

end RotationBST.Tango.Combination
