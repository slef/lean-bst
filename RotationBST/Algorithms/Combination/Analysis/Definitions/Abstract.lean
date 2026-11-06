module

public import RotationBST.Algorithms.Combination.Worker.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Analysis

abbrev Charges := Bool → List Nat → Nat → ℝ

def segment (xs : List Nat) (lo hi : Nat) : List Nat := (xs.drop lo).take (hi - lo)
def mass (charges : Charges) (side : Bool) (xs : List Nat) (lo hi : Nat) : ℝ :=
  ∑ i ∈ Finset.Ico lo hi, charges side xs i

def total (charges : Charges) (side : Bool) (xs : List Nat) : ℝ := mass charges side xs 0 xs.length

/-- Well-behaved amortized bounds in the operational worker model. `upper`
includes the one-time overhead, `stable` compares a standalone contiguous
segment with its original charges, and `single` bounds every valid access
from any reachable request boundary. Charges are explicitly nonnegative. -/
structure WellBehaved {σ : Type} (worker : Controller.Worker σ) (n overhead C₀ C₁ : Nat) (charges : Charges) : Prop where
  nonneg : ∀ side xs i, 0 ≤ charges side xs i
  single : ∀ side earlier state spent, Worker.Requests worker side (worker.restart side) earlier state spent →
    (∀ x ∈ earlier, x < n) → ∀ x, x < n →
      ∃ final cost, Worker.Access worker side state x final cost ∧ cost ≤ C₁ * overhead
  upper : ∀ side xs, (∀ x ∈ xs, x < n) →
    ∃ final cost, Worker.Requests worker side (worker.restart side) xs final cost ∧
      (cost : ℝ) ≤ total charges side xs + overhead
  stable : ∀ side xs, (∀ x ∈ xs, x < n) → ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
    total charges side (segment xs lo hi) + overhead ≤ C₀ * mass charges side xs lo hi + C₁ * overhead

/-- A round budget strictly exceeds the per-access/segment overhead factor. -/
def budget (overhead C₁ : Nat) : Nat := (C₁ + 1) * overhead

end RotationBST.Combo.Analysis
