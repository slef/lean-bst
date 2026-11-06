module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract
public import Mathlib.Order.Lattice.Nat

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Minimum

/-- The least total potential among representations of the same labelled
source cursor. This depends on the fixed analysis weights, not on future input.
For an unrepresentable cursor, the natural-number infimum is zero. -/
noncomputable def potential {α : Type} (weight : α → ℝ) (c : LabelledCursor.Config α) : Nat :=
  sInf {n | ∃ s : State α, ConfigValid weight c s ∧ s.potential = n}

/-- Credit above the minimum for this source cursor. Minimum representations
start with zero excess even when every representation has positive raw credit. -/
noncomputable def excess {α : Type} (weight : α → ℝ) (c : LabelledCursor.Config α)
    (s : State α) : Nat := s.potential - potential weight c

end RotationBST.HeavyPath.Finger.History.Simulation.Minimum
