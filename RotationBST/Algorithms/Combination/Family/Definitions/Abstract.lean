module

public import RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract
public import Mathlib.Data.Fintype.Pi

@[expose] public section
namespace RotationBST.Combo.Family

/-- An interruptible online BST with its actual pointer interpretation and
request correctness. The state type may differ between family members. -/
structure Algorithm (saved : Tree) where
  State : Type
  worker : Controller.Worker State
  model : Refinement.WorkerModel worker saved
  correct : Refinement.Visits.Correct model

/-- A comparator assigns a nonnegative amortized charge to each request. -/
abbrev Charge := List Nat → Nat → ℝ

/-- Leaves of a full binary combination tree of the given depth. -/
abbrev Index (depth : Nat) := Fin depth → Bool

/-- Uniform charge expansion after a fixed number of combination levels. -/
def chargeScale (C₀ C₁ : Nat) : Nat → Nat
  | 0 => 1
  | depth + 1 => Online.Replay.chargeFactor C₀ (C₁ + depth) 57 * chargeScale C₀ C₁ depth

/-- Uniform overhead expansion; all leaves use the same initial overhead. -/
def overheadScale (C₀ C₁ : Nat) : Nat → Nat
  | 0 => 1
  | depth + 1 => Online.Replay.overheadFactor C₀ (C₁ + depth) 57 * overheadScale C₀ C₁ depth

/-- One fixed worker retains a well-behaved bound against every listed
comparator. Its execution is independent of the comparator index. -/
def Guarantees {ι : Type} {saved : Tree} (algorithm : Algorithm saved)
    (overhead C₀ C₁ factor : Nat) (charges : ι → Charge) : Prop :=
  ∀ i, Analysis.WellBehaved algorithm.worker saved.size overhead C₀ C₁
    (fun _ xs t => (factor : ℝ) * charges i xs t)

/-- The original total amortized charge, without any combination factor. -/
def total (charge : Charge) (xs : List Nat) : ℝ :=
  Analysis.total (fun _ => charge) false xs

/-- The least original total charge among a nonempty finite family. -/
noncomputable def minimum {ι : Type} [Fintype ι] [Nonempty ι]
    (charges : ι → Charge) (xs : List Nat) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => total (charges i) xs)

end RotationBST.Combo.Family
