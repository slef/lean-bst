module

public import RotationBST.Algorithms.Combination.Family.Physical.Windows
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Family.Physical

/-- The whole prefix is a window starting at the uninitialized boundary. Its
preparation charge is included in the same uniform bound. -/
theorem prefix_minimum {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.current (Online.execute p none xs).1) (Online.execute p none xs).2 ∧
      ((Online.execute p none xs).2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * Family.minimum charges xs +
        (overheadFactor C₀ C₁ * overhead : Nat) := by
  have bound := window_minimum algorithm guaranteed p size xs valid 0 xs.length (Nat.zero_le _) le_rfl
  have segment : Analysis.segment xs 0 xs.length = xs := by simp [Analysis.segment]
  simp only [List.take_zero, Online.execute, segment, Online.Prepared.current] at bound
  exact ⟨bound.2.1, by simpa only [minimumMass, Family.minimum, mass, total, Analysis.total] using bound.2.2⟩

/-- One prepared policy has all future prefix and window guarantees. -/
theorem bounded {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead) :
    Bounded p (chargeFactor C₀ C₁ factor) (overheadFactor C₀ C₁ * overhead) charges := by
  intro xs valid
  have prefixBound := prefix_minimum algorithm guaranteed p size xs valid
  exact ⟨prefixBound.1, prefixBound.2, fun lo hi ordered inside =>
    window_minimum algorithm guaranteed p size xs valid lo hi ordered inside⟩

/-- Choose the final physical policy once. Any comparator may supply its
existence contract, and every comparator then bounds that same policy. -/
theorem policy_exists {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      Bounded p (chargeFactor C₀ C₁ factor) (overheadFactor C₀ C₁ * overhead) charges := by
  let reference : ι := Classical.choice inferInstance
  obtain ⟨p, _⟩ := Online.Results.prefix_policy algorithm.model algorithm.correct (guaranteed reference)
    nonempty size fields oldData
  exact ⟨p, bounded algorithm guaranteed p size⟩

/-- Fixed-family combination followed by one physical-policy wrapper. Both
choices precede every request sequence and every measured window. -/
theorem combine {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∃ p : Online.Prepared output.model (Analysis.budget (overheadScale C₀ C₁ depth * overhead) (C₁ + depth))
          (57 * (overheadScale C₀ C₁ depth * overhead)) fields oldData,
        Bounded p (chargeFactor C₀ (C₁ + depth) (chargeScale C₀ C₁ depth))
          (overheadFactor C₀ (C₁ + depth) * (overheadScale C₀ C₁ depth * overhead)) charges := by
  obtain ⟨output, guaranteed⟩ := Family.Results.finite depth overhead C₀ C₁ capacity
    inputs charges well nonempty size fields oldData
  have levelSize : saved.size ≤ overheadScale C₀ C₁ depth * overhead :=
    size.trans (Nat.le_mul_of_pos_left _ (Family.Results.overheadScale_pos C₀ C₁ depth))
  exact ⟨output, guaranteed, policy_exists output guaranteed nonempty levelSize fields oldData⟩

/-- Any nonempty finite family has a single physical online policy with
minimum bounds on every prefix and every actual contiguous execution window. -/
theorem finite_policy {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    let depth := Nat.clog 2 (Fintype.card ι)
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∃ p : Online.Prepared output.model (Analysis.budget (overheadScale C₀ C₁ depth * overhead) (C₁ + depth))
          (57 * (overheadScale C₀ C₁ depth * overhead)) fields oldData,
        Bounded p (chargeFactor C₀ (C₁ + depth) (chargeScale C₀ C₁ depth))
          (overheadFactor C₀ (C₁ + depth) * (overheadScale C₀ C₁ depth * overhead)) charges :=
  combine _ overhead C₀ C₁ (Nat.le_pow_clog (by decide) _) inputs charges well nonempty size fields oldData

end RotationBST.Combo.Family.Physical
