module

public import RotationBST.Algorithms.GreedyASS.Combination.Inputs
public import RotationBST.Algorithms.Combination.Online.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination
open Combo

/-- One combined policy, with its prepared physical state and replay worker,
exists before any reference tree, request sequence, or offline comparator. -/
theorem policy_exists (saved : Tree) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    Nonempty (Policy saved fields oldData) := by
  obtain ⟨left, right, supported⟩ := paired_inputs saved
  have correct : Refinement.Visits.Correct (pairModel left right) :=
    Worker.Pair.Results.correct (Worker.Replay.model left) (Worker.Replay.model right) false false
      (Worker.Replay.Results.correct left) (Worker.Replay.Results.correct right)
  obtain ⟨p, implementation, _correct, _well⟩ := Online.Replay.Results.combine (pairModel left right)
    correct (supported saved rfl) nonempty (size_le_overhead saved) fields oldData
  exact ⟨⟨left, right, supported, p, implementation⟩⟩

/-- The same physical execution satisfies the minimum bound for every fixed
lazy-finger reference. Startup is charged once, within `overhead saved`. -/
theorem Policy.tree_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (reference : Tree) (same : reference.size = saved.size)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.finalTree xs) (p.cost xs) ∧
      (p.cost xs : ℝ) ≤ 1307904 * min (46225920 * (LazyFinger.cost reference xs : ℝ))
        (Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
          (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat)) +
        2531968 * overhead saved := by
  obtain ⟨execution, bound⟩ := Online.Results.minimum_bound (p.supported reference same) p.prepared xs valid
  have leftTotal : Analysis.total (charges saved reference) false xs =
      46225920 * (LazyFinger.cost reference xs : ℝ) :=
    Charges.Results.lazyFinger_total 46225920 reference false xs
  have rightTotal : Analysis.total (charges saved reference) true xs =
      Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
        (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat) :=
    Charges.Results.interleave_total _ _ true xs
  rw [leftTotal, rightTotal] at bound
  have size : (saved.size : ℝ) ≤ overhead saved := by exact_mod_cast size_le_overhead saved
  refine ⟨execution, ?_⟩
  change (p.cost xs : ℝ) ≤ _ at bound
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, one_mul] at bound ⊢
  nlinarith

/-- Minimize the lazy-finger analysis after fixing the physical policy. -/
theorem Policy.optimal_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.finalTree xs) (p.cost xs) ∧
      (p.cost xs : ℝ) ≤ 1307904 * min (46225920 * (LazyFinger.optimalCost saved.size xs : ℝ))
        (Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
          (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat)) +
        2531968 * overhead saved := by
  obtain ⟨reference, same, optimal⟩ := LazyFinger.Results.optimal_attained saved.size xs
  simpa only [optimal] using p.tree_bound reference same xs valid

/-- The already chosen replay worker inherits every reference bound and either
source comparator, and remains a valid input for further combination. -/
theorem Policy.worker_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (reference : Tree) (same : reference.size = saved.size)
    (select : Bool → Bool) :
    Analysis.WellBehaved (Worker.Replay.worker p.implementation.planner) saved.size
      (Online.Replay.overheadFactor 1 20 57 * overhead saved) 1 21
      (Online.Replay.scaledCharges (Online.Replay.chargeFactor 1 20 57)
        (fun side => charges saved reference (select side))) :=
  Online.Replay.Results.well_behaved_selection (p.supported reference same) p.prepared p.implementation
    (size_le_overhead saved) select

end RotationBST.Geometric.GreedyASS.Combination
