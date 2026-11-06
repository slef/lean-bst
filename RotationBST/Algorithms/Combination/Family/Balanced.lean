module

public import RotationBST.Algorithms.Combination.Family.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Online.Replay.Abstract
public import RotationBST.Algorithms.Combination.Worker.Pair.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Family

theorem overheadScale_pos (C₀ C₁ depth : Nat) : 0 < overheadScale C₀ C₁ depth := by
  induction depth with
  | zero => exact Nat.zero_lt_one
  | succ depth ih =>
    exact Nat.mul_pos (by unfold Online.Replay.overheadFactor; omega) ih

/-- Choose one online algorithm for all leaves of a fixed balanced tree.
Every original comparator is retained, including contiguous-segment stability,
so the result can itself be used in another combination. -/
theorem balanced {saved : Tree} (depth overhead C₀ C₁ : Nat)
    (inputs : Index depth → Algorithm saved) (charges : Index depth → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges := by
  induction depth with
  | zero =>
    refine ⟨inputs (fun _ => false), ?_⟩
    intro i
    have same : i = fun _ => false := by funext j; exact Fin.elim0 j
    subst i
    simpa [chargeScale, overheadScale] using well (fun _ => false)
  | succ depth ih =>
    obtain ⟨left, leftWell⟩ := ih (fun i => inputs (Fin.cons false i)) (fun i => charges (Fin.cons false i))
      (fun i => well (Fin.cons false i))
    obtain ⟨right, rightWell⟩ := ih (fun i => inputs (Fin.cons true i)) (fun i => charges (Fin.cons true i))
      (fun i => well (Fin.cons true i))
    let paired := Worker.Pair.model left.model right.model false false
    have correct : Refinement.Visits.Correct paired :=
      Worker.Pair.Results.correct left.model right.model false false left.correct right.correct
    have pairWell := fun i j => Worker.Pair.Results.well_behaved (leftWell i) (rightWell j) false false
    have levelSize : saved.size ≤ overheadScale C₀ C₁ depth * overhead :=
      size.trans (Nat.le_mul_of_pos_left _ (overheadScale_pos C₀ C₁ depth))
    obtain ⟨p, implementation, implementedCorrect, _⟩ := Online.Replay.Results.combine paired correct
      (pairWell (fun _ => false) (fun _ => false)) nonempty levelSize fields oldData
    refine ⟨⟨_, Worker.Replay.worker implementation.planner, Worker.Replay.model implementation.planner,
      implementedCorrect⟩, ?_⟩
    intro i
    have split : Fin.cons (i 0) (Fin.tail i) = i := Fin.cons_self_tail i
    cases bit : i 0 with
    | false =>
      have inherited := Online.Replay.Results.well_behaved_selection (restoreFactor := 57)
        (pairWell (Fin.tail i) (fun _ => false)) p implementation levelSize (fun _ => false)
      unfold Online.Replay.scaledCharges at inherited
      rw [bit] at split
      simpa only [Guarantees, chargeScale, overheadScale, Online.Replay.scaledCharges,
        Worker.Pair.charges, Nat.add_assoc, Nat.cast_mul, mul_assoc, split, Bool.false_eq_true, ite_false, ite_true] using inherited
    | true =>
      have inherited := Online.Replay.Results.well_behaved_selection (restoreFactor := 57)
        (pairWell (fun _ => false) (Fin.tail i)) p implementation levelSize (fun _ => true)
      unfold Online.Replay.scaledCharges at inherited
      rw [bit] at split
      simpa only [Guarantees, chargeScale, overheadScale, Online.Replay.scaledCharges,
        Worker.Pair.charges, Nat.add_assoc, Nat.cast_mul, mul_assoc, split, Bool.false_eq_true, ite_false, ite_true] using inherited

end RotationBST.Combo.Family
