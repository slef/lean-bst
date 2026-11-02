module

public import RotationBST.Model.Abstract

@[expose] public section

/-! Endpoint-labelled rotations for the pending lazy-simulation argument.
These definitions do not assert that the full simulation is established. -/
namespace RotationBST.Pointer.Lazy

/-- `RotateAt x y` promotes key `x` over its parent `y`. -/
inductive RotateAt {α : Type} : α → α → LabelledTree α → LabelledTree α → Prop where
  | right {a b c : LabelledTree α} {x y : α} :
      RotateAt x y (.node (.node a x b) y c) (.node a x (.node b y c))
  | left {a b c : LabelledTree α} {x y : α} :
      RotateAt x y (.node a y (.node b x c)) (.node (.node a y b) x c)
  | inLeft {a b c : LabelledTree α} {x y z : α} :
      RotateAt x y a b → RotateAt x y (.node a z c) (.node b z c)
  | inRight {a b c : LabelledTree α} {x y z : α} :
      RotateAt x y a b → RotateAt x y (.node c z a) (.node c z b)

/-- The two rotations have no endpoint key in common. -/
def DisjointPairs {α : Type} (x y u v : α) : Prop :=
  x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v

/-- A rotation program records the two endpoint keys of every instruction. -/
inductive Trace {α : Type} : LabelledTree α → List (α × α) → LabelledTree α → Prop where
  | nil {t : LabelledTree α} : Trace t [] t
  | cons {x y : α} {s t u : LabelledTree α} {ops : List (α × α)} :
      RotateAt x y s t → Trace t ops u → Trace s ((x, y) :: ops) u

/-- The explicit key at a labelled tree's root. -/
def rootKey? {α : Type} : LabelledTree α → Option α
  | .nil => none
  | .node _ x _ => some x

end RotationBST.Pointer.Lazy
