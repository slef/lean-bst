module

public import RotationBST.Algorithms.Combination.Online.Replay.Bounds
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Online.Replay

/-- The implemented combined policy is itself a well-behaved interruptible
worker. Each output side may be compared with either original charge function.
The implementation is fixed independently of this proof-side selection. -/
theorem well_behaved_selection {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (size : saved.size ≤ overhead) (select : Bool → Bool) :
    Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
      (overheadFactor C₀ C₁ restoreFactor * overhead) C₀ (C₁ + 1)
      (scaledCharges (chargeFactor C₀ C₁ restoreFactor) (fun side => charges (select side))) := by
  have factors := factor_bounds C₀ C₁ restoreFactor
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro side xs i
    exact mul_nonneg (Nat.cast_nonneg _) (well.nonneg (select side) xs i)
  · intro side earlier state spent ran earlierValid x valid
    obtain ⟨final, cost, accessRun, bound⟩ := single p implementation side state x
      ⟨earlier, spent, ran, earlierValid⟩ valid
    refine ⟨final, cost, accessRun, ?_⟩
    calc
      cost ≤ 1140224 * overhead + 16768 * (2 * Analysis.budget overhead C₁ + restoreFactor * overhead) := by omega
      _ = (16768 * (68 + 2 * (C₁ + 1) + restoreFactor)) * overhead := by simp only [Analysis.budget]; ring
      _ ≤ overheadFactor C₀ C₁ restoreFactor * overhead := Nat.mul_le_mul_right _ factors.2.2
      _ ≤ (C₁ + 1) * (overheadFactor C₀ C₁ restoreFactor * overhead) := Nat.le_mul_of_pos_left _ (by omega)
  · intro side xs valid
    obtain ⟨cost, ran, bound⟩ := minimum_bound well p implementation side xs valid
    refine ⟨_, cost, ran, ?_⟩
    have smaller : min (Analysis.total charges false xs) (Analysis.total charges true xs) ≤ Analysis.total charges (select side) xs := by
      cases select side <;> simp only [min_le_left, min_le_right]
    have sizeReal : (saved.size : ℝ) ≤ overhead := by exact_mod_cast size
    have factorReal : (16768 * (68 + 3 * (C₁ + 1 + restoreFactor)) : ℝ) ≤ overheadFactor C₀ C₁ restoreFactor := by
      exact_mod_cast factors.2.1
    calc
      (cost : ℝ) ≤ 1140224 * (saved.size : ℝ) + 16768 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := bound
      _ ≤ 1140224 * (overhead : ℝ) + 16768 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * Analysis.total charges (select side) xs + 3 * overhead) := by gcongr
      _ = (chargeFactor C₀ C₁ restoreFactor : ℝ) * Analysis.total charges (select side) xs +
          (16768 * (68 + 3 * (C₁ + 1 + restoreFactor)) : ℝ) * overhead := by
        simp only [chargeFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        ring
      _ ≤ (chargeFactor C₀ C₁ restoreFactor : ℝ) * Analysis.total charges (select side) xs +
          (overheadFactor C₀ C₁ restoreFactor : ℝ) * overhead := by gcongr
      _ = Analysis.total (scaledCharges (chargeFactor C₀ C₁ restoreFactor) (fun side => charges (select side))) side xs +
          (overheadFactor C₀ C₁ restoreFactor * overhead : Nat) := by rw [scaled_total]; norm_cast
  · intro side xs valid lo hi ordered inside
    have stable := well.stable (select side) xs valid lo hi ordered inside
    have scaled := mul_le_mul_of_nonneg_left stable (Nat.cast_nonneg (chargeFactor C₀ C₁ restoreFactor))
    have factorReal : (chargeFactor C₀ C₁ restoreFactor : ℝ) ≤ overheadFactor C₀ C₁ restoreFactor := by
      exact_mod_cast factors.1
    have allowance := mul_le_mul_of_nonneg_right factorReal (show (0 : ℝ) ≤ C₁ * overhead by positivity)
    have nonnegative : (0 : ℝ) ≤ (chargeFactor C₀ C₁ restoreFactor : ℝ) * overhead := by positivity
    rw [scaled_total, scaled_mass]
    dsimp only [Analysis.total, Analysis.mass] at scaled ⊢
    push_cast at scaled allowance ⊢
    nlinarith only [scaled, allowance, nonnegative]

/-- The implemented combined policy is itself a well-behaved interruptible
worker. Each side inherits its corresponding original charge function, scaled
uniformly; neither side selects a comparator using future requests. -/
theorem well_behaved {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (size : saved.size ≤ overhead) :
    Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
      (overheadFactor C₀ C₁ restoreFactor * overhead) C₀ (C₁ + 1)
      (scaledCharges (chargeFactor C₀ C₁ restoreFactor) charges) :=
  well_behaved_selection well p implementation size id

end RotationBST.Combo.Online.Replay
