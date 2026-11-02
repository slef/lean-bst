module

public import RotationBST.Geometry.AbstractBridge

@[expose] public section

/-! # Rotation connectivity

All definitions in these statements appear in `Model/Abstract.lean`.
The bound counts rotations, including those below the root; it is not a
pointer-travel bound.
-/
namespace RotationBST.Geometry

variable {x k : Nat}

/-- Any two shapes on the same number of keys are connected by at most `2n`
rotations. The initial and final shapes are prescribed, including when empty. -/
theorem reset (s t : Tree) (h : s.size = t.size) :
    ∃ k, k ≤ 2 * s.size ∧ Rotations s t k :=
  reset_linear s t h

/-- A reset may be charged before an access while retaining its requested root. -/
theorem reset_before_access (s t u : Tree) (h : s.size = t.size)
    (ha : Access t u x k) :
    ∃ j, j ≤ 2 * s.size ∧ Access s u x (j + k) :=
  reset_then_access s t u h ha

end RotationBST.Geometry
