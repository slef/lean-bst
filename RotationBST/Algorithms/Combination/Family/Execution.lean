module

public import RotationBST.Algorithms.Combination.Family.Finite
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Family

/-- All comparator bounds hold for the very same completed execution. The
uniqueness of deterministic worker runs rules out comparator-dependent costs
or successor states. -/
theorem requests {ι : Type} [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final cost, Worker.Requests algorithm.worker side (algorithm.worker.restart side) xs final cost ∧
      ∀ i, (cost : ℝ) ≤ (factor : ℝ) * total (charges i) xs + overhead := by
  let first : ι := Classical.choice inferInstance
  obtain ⟨final, cost, ran, _⟩ := (guaranteed first).upper side xs valid
  refine ⟨final, cost, ran, ?_⟩
  intro i
  obtain ⟨other, otherCost, otherRun, bound⟩ := (guaranteed i).upper side xs valid
  have same := Worker.Results.Requests.unique ran otherRun
  rw [← same.2] at bound
  simpa only [total, Analysis.total, Analysis.mass, Finset.mul_sum] using bound

/-- The all-comparator execution bound is the usual minimum-of-family bound.
The minimizing index is used only in the proof, after the run has been fixed. -/
theorem minimum_bound {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (algorithm : Algorithm saved) {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final cost, Worker.Requests algorithm.worker side (algorithm.worker.restart side) xs final cost ∧
      (cost : ℝ) ≤ (factor : ℝ) * minimum charges xs + overhead := by
  obtain ⟨final, cost, ran, bounds⟩ := requests algorithm guaranteed side xs valid
  obtain ⟨i, _, least⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
    (fun i => total (charges i) xs)
  exact ⟨final, cost, ran, by simpa only [minimum, least] using bounds i⟩

/-- The fixed-family prefix theorem, with one algorithm chosen before the
request sequence and a single actual run bounded against every input. -/
theorem combine {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        ∃ final cost, Worker.Requests output.worker side (output.worker.restart side) xs final cost ∧
          ∀ i, (cost : ℝ) ≤ (chargeScale C₀ C₁ depth : ℝ) * total (charges i) xs +
            (overheadScale C₀ C₁ depth * overhead : Nat) := by
  obtain ⟨output, guaranteed⟩ := finite depth overhead C₀ C₁ capacity inputs charges well nonempty size fields oldData
  exact ⟨output, guaranteed, fun side xs valid => requests output guaranteed side xs valid⟩

/-- A ceiling-logarithmic-depth combination satisfies the minimum bound on
all future prefixes, while retaining the full reusable well-behaved contract. -/
theorem minimum_policy {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead)
        C₀ (C₁ + Nat.clog 2 (Fintype.card ι)) (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι))) charges ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        ∃ final cost, Worker.Requests output.worker side (output.worker.restart side) xs final cost ∧
          (cost : ℝ) ≤ (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) : ℝ) * minimum charges xs +
            (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead : Nat) := by
  obtain ⟨output, guaranteed⟩ := exists_combination overhead C₀ C₁ inputs charges well nonempty size fields oldData
  exact ⟨output, guaranteed, fun side xs valid => minimum_bound output guaranteed side xs valid⟩

end RotationBST.Combo.Family
