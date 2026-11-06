module

public import RotationBST.Algorithms.Combination.Family.Physical.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Family.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Family.Physical

/-- Every original comparator bounds the same actual physical window. The
policy is already fixed, and the left boundary carries its real controller and
hand state. The three costs add to the complete execution cost exactly. -/
theorem executed_window {ι : Type} [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := Online.execute p none (xs.take lo)
    let middle := Online.execute p first.1 (Analysis.segment xs lo hi)
    let last := Online.execute p middle.1 (xs.drop hi)
    Online.execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      ∀ i, (middle.2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * mass (charges i) xs lo hi +
        (overheadFactor C₀ C₁ * overhead : Nat) := by
  let reference : ι := Classical.choice inferInstance
  have firstBound := Online.Results.executed_window (restoreFactor := 57)
    (guaranteed reference) p xs valid lo hi ordered inside
  refine ⟨firstBound.1, firstBound.2.1, ?_⟩
  intro i
  have bound := (Online.Results.executed_window (restoreFactor := 57)
    (guaranteed i) p xs valid lo hi ordered inside).2.2
  have scaled (side : Bool) : Analysis.mass (fun _ ys t => (factor : ℝ) * charges i ys t) side xs lo hi =
      (factor : ℝ) * mass (charges i) xs lo hi := by
    simp only [mass, Analysis.mass, Finset.mul_sum]
  simp only [scaled, min_self] at bound
  have sizeReal : (saved.size : ℝ) ≤ overhead := by exact_mod_cast size
  have positive : (1 : ℝ) ≤ (C₁ + 1 + 57 : Nat) := by exact_mod_cast (show 1 ≤ C₁ + 1 + 57 by omega)
  have allowance := mul_le_mul_of_nonneg_right positive (Nat.cast_nonneg overhead)
  calc
    _ ≤ 570112 * (saved.size : ℝ) + 8384 * (C₁ + 1 + 57 : Nat) *
        (2 * C₀ * C₀ * ((factor : ℝ) * mass (charges i) xs lo hi) +
          (2 * C₀ * C₁ + 5) * overhead) := bound
    _ ≤ 8384 * (C₁ + 1 + 57 : Nat) *
        (2 * C₀ * C₀ * ((factor : ℝ) * mass (charges i) xs lo hi) +
          (2 * C₀ * C₁ + 73) * overhead) := by nlinarith only [sizeReal, allowance]
    _ = _ := by simp only [chargeFactor, overheadFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; ring

/-- Taking the least comparator changes only the bound, never the policy or
any boundary of the executed physical window. -/
theorem window_minimum {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := Online.execute p none (xs.take lo)
    let middle := Online.execute p first.1 (Analysis.segment xs lo hi)
    let last := Online.execute p middle.1 (xs.drop hi)
    Online.execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      (middle.2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * minimumMass charges xs lo hi +
        (overheadFactor C₀ C₁ * overhead : Nat) := by
  obtain ⟨split, physical, bounds⟩ := executed_window algorithm guaranteed p size xs valid lo hi ordered inside
  obtain ⟨i, _, least⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun i => mass (charges i) xs lo hi)
  exact ⟨split, physical, by simpa only [minimumMass, least] using bounds i⟩

end RotationBST.Combo.Family.Physical
