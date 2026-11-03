module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! Move-to-root, the simplest self-adjusting rule: the requested rank is
rotated upward one level at a time until it is the root. It is a baseline for
comparison, not a substitute for splaying. -/
namespace RotationBST

/-- Recursively expose x in its child subtree, then rotate it one level up.
Out-of-range inputs have arbitrary behavior; correctness is required only in range. -/
def moveToRoot : Tree → Nat → Tree × Nat
  | .nil, _ => (.nil, 0)
  | .node l r, x =>
      if x < l.size then
        let (u, k) := moveToRoot l x
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node a (.node b r), k + 1)
      else if x = l.size then (.node l r, 0)
      else
        let (u, k) := moveToRoot r (x - l.size - 1)
        match u with
        | .nil => (.node l r, 0)
        | .node a b => (.node (.node l a) b, k + 1)

end RotationBST
