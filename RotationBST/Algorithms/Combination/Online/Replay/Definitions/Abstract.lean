module

public import RotationBST.Algorithms.Combination.Online.Algorithm.Abstract
public import RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract
public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Online.Replay

/-- A fixed replay implementation of the already chosen combined policy.
Both worker sides run the same policy; inherited bounds may be chosen separately. -/
structure Implementation {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Prepared model budget restore fields oldData) where
  planner : Worker.Replay.Planner (Option (Online.State model p.data budget)) saved
  initial : planner.initial = fun _ => none
  tree : planner.tree = fun _ => p.current
  expansion : ∀ side state x, x < saved.size →
    (planner.plan side state x).1 = (access p state x).1 ∧
    (planner.plan side state x).2.length + 2 ≤ 2 * (access p state x).2

def chargeFactor (C₀ C₁ restoreFactor : Nat) : Nat := 16768 * (C₁ + 1 + restoreFactor) * (2 * C₀)

def overheadFactor (C₀ C₁ restoreFactor : Nat) : Nat :=
  chargeFactor C₀ C₁ restoreFactor +
    16768 * (68 + 3 * (C₁ + 1 + restoreFactor) + 2 * (C₁ + 1) + restoreFactor) + 1

def scaledCharges (factor : Nat) (charges : Analysis.Charges) : Analysis.Charges :=
  fun side xs i => factor * charges side xs i

end RotationBST.Combo.Online.Replay
