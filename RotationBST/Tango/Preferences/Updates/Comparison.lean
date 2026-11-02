module

public import RotationBST.Tango.Preferences.Updates.Validity
public import RotationBST.Tango.Wilber.Bound
public import RotationBST.Access.AbstractBridge

@[expose] public section
namespace RotationBST.Tango

/-- The number of actual preference updates is bounded against every offline
rotation execution. Each update still has to be realized by marked-tree edits. -/
theorem preferenceLog_le_rotations (reference : Tree) {s t : Tree} {xs : List Nat} {r : Nat}
    (size : reference.size = s.size) (execution : RotationBST.Execution s xs t r) :
    (preferenceLog reference [] xs).length ≤ 4 * r + 2 * xs.length + reference.size := by
  have valid : ∀ x ∈ xs, x < reference.size := by
    rw [size]
    exact AccessBridge.execution_valid execution
  have h := preferenceLog_bound reference xs valid
  have lower := Wilber.interleave_le_rotations reference size execution
  omega

end RotationBST.Tango
