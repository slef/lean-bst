module

public import RotationBST.WorkingSet.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Dist

@[expose] public section

/-! Elementary sequence costs and asymptotic properties. Logs are base two.
All constants are uniform natural numbers, and startup is explicitly charged. -/
namespace RotationBST

/-- Frequency entropy, with one unit per request. Zero-frequency terms vanish. -/
noncomputable def Bounds.staticCost (n : Nat) (xs : List Nat) : ℝ :=
  (xs.length : ℝ) + ∑ x ∈ Finset.range n,
    (xs.count x : ℝ) * Real.logb 2 ((xs.length : ℝ) / xs.count x)

/-- Static optimality in the frequency-entropy formulation, with the same
`n(1 + floor(log₂ n))` initialization allowance as the working-set property. -/
def HasStaticOptimalityBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
    (a.totalCost t xs : ℝ) ≤ (C : ℝ) * Bounds.staticCost t.size xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ))

/-- Static finger cost for the fixed inorder rank `f`, including one unit per request. -/
noncomputable def Bounds.fingerCost (f : Nat) (xs : List Nat) : ℝ :=
  (xs.map fun x : Nat => 1 + Real.logb 2 (Nat.dist x f + 1 : Nat)).sum

/-- The constant factors are uniform over the initial tree, request sequence,
and choice of fixed finger. -/
def HasStaticFingerBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs f, f < t.size → (∀ x ∈ xs, x < t.size) →
    (a.totalCost t xs : ℝ) ≤ (C : ℝ) * Bounds.fingerCost f xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ))

end RotationBST
