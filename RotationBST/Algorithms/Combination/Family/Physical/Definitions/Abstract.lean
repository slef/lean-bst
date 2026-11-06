module

public import RotationBST.Algorithms.Combination.Family.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Family.Physical

/-- Original comparator charges on a window of the original sequence. The
indices and history are retained, rather than recomputed on the slice. -/
def mass (charge : Charge) (xs : List Nat) (lo hi : Nat) : ℝ :=
  Analysis.mass (fun _ => charge) false xs lo hi

/-- Least original window charge in a nonempty finite family. -/
noncomputable def minimumMass {ι : Type} [Fintype ι] [Nonempty ι]
    (charges : ι → Charge) (xs : List Nat) (lo hi : Nat) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => mass (charges i) xs lo hi)

/-- Physical window-charge coefficient of the final policy wrapper. -/
def chargeFactor (C₀ C₁ factor : Nat) : Nat :=
  8384 * (C₁ + 1 + 57) * (2 * C₀ * C₀) * factor

/-- Physical window overhead, including preparation or carried potential. -/
def overheadFactor (C₀ C₁ : Nat) : Nat :=
  8384 * (C₁ + 1 + 57) * (2 * C₀ * C₁ + 73)

/-- Uniform prefix and actual-window guarantees for one already chosen policy.
The window cost is part of the original execution, with exact boundary states
and additive splitting. Comparators retain the original sequence's history. -/
def Bounded {ι : Type} [Fintype ι] [Nonempty ι]
    {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared model budget restore fields oldData) (factor overhead : Nat)
    (charges : ι → Charge) : Prop :=
  ∀ xs, (∀ x ∈ xs, x < saved.size) →
    Pointer.Execution saved xs (p.current (Online.execute p none xs).1) (Online.execute p none xs).2 ∧
      ((Online.execute p none xs).2 : ℝ) ≤ (factor : ℝ) * Family.minimum charges xs + overhead ∧
      ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
        let first := Online.execute p none (xs.take lo)
        let middle := Online.execute p first.1 (Analysis.segment xs lo hi)
        let last := Online.execute p middle.1 (xs.drop hi)
        Online.execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
          Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
          (middle.2 : ℝ) ≤ (factor : ℝ) * minimumMass charges xs lo hi + overhead

end RotationBST.Combo.Family.Physical
