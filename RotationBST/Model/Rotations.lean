module

public import RotationBST.Model.Basic

@[expose] public section

namespace RotationBST

variable {s t u l r : Tree} {k m : Nat}

namespace Rotations

theorem append (h : Rotations s t k) (g : Rotations t u m) : Rotations s u (k + m) := by
  induction h with
  | refl => simpa using g
  | step h _ ih => simpa only [Nat.add_assoc, Nat.add_comm 1 m] using Rotations.step h (ih g)

theorem inLeft (h : Rotations s t k) : Rotations (.node s r) (.node t r) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (.inLeft h) ih

theorem inRight (h : Rotations s t k) : Rotations (.node l s) (.node l t) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (.inRight h) ih

end Rotations

end RotationBST
