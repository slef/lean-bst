module

public import RotationBST.Algorithms.Combination.Online.Replay.Inheritance

@[expose] public section
namespace RotationBST.Combo.Online.Replay

/-- Choose the combined policy and its interruptible implementation before
any requests. The result has both the pointer correctness contract and the
well-behaved bounds required of another combination input. -/
theorem combine {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∃ implementation : Implementation p,
        Refinement.Visits.Correct (Worker.Replay.model implementation.planner) ∧
        Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
          (overheadFactor C₀ C₁ 57 * overhead) C₀ (C₁ + 1)
          (scaledCharges (chargeFactor C₀ C₁ 57) charges) := by
  obtain ⟨p, _⟩ := Online.Results.prefix_policy model correct well nonempty size fields oldData
  obtain ⟨implementation⟩ := implementation_exists p
  exact ⟨p, implementation, Worker.Replay.Results.correct implementation.planner,
    well_behaved well p implementation size⟩

end RotationBST.Combo.Online.Replay
