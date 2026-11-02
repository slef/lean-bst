module

public import RotationBST.Normalization.AbstractBridge

@[expose] public section

/-! # Counting requests as well as rotations

The working-set definitions are in `WorkingSet/Abstract.lean`; algorithm and
competitive-cost definitions are in `Online/Abstract.lean`. The `1 + log₂`
convention makes the working-set statement insensitive to this normalization.
No algorithm's working-set bound is asserted here.
-/
namespace RotationBST

/-- Charging one unit per request does not change which algorithms satisfy our
working-set bound. Constants are uniform over initial trees and valid sequences. -/
theorem workingSet_totalCost_iff (a : Algorithm) :
    HasWorkingSetBound a ↔
      ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
        a.totalCost t xs ≤ C * workingSetSum t.size [] xs +
          D * t.size * (1 + t.size.log2) :=
  BoundsBridge.normalized_workingSet_iff a

/-- Rotation-only competitiveness implies conventional total-cost competitiveness.
The converse is deliberately not asserted: requests can have zero rotations. -/
theorem DynamicallyOptimal.total (a : Algorithm) (h : DynamicallyOptimal a) :
    TotallyDynamicallyOptimal a :=
  BoundsBridge.total_dynamic a h

end RotationBST
