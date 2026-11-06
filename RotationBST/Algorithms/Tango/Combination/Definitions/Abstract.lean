module

public import RotationBST.Algorithms.Tango.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.Tango.Combination

/-- Uniform simulation coefficient for the existing Tango upper bound.
For a balanced reference it grows doubly logarithmically in its size.
The corresponding initialization allowance is `chargeFactor reference * n`;
the sharper bottom-up adapter below instead has a separate linear allowance. -/
noncomputable def chargeFactor (reference : Tree) : Nat :=
  ⌈64 * (14 * Real.logb 2 (height reference) + 6)⌉₊

/-- Simulation coefficient for the bottom-up policy. Startup is accounted
separately by a constant times n, rather than by this coefficient times n. -/
noncomputable def linearChargeFactor (reference : Tree) : Nat := 2 * chargeFactor reference

end RotationBST.Tango.Combination
