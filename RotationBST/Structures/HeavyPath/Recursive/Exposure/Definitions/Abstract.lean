module

public import RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.Exposure
open Paired

/-- The residual heavy path is retained explicitly after exposing its source
root. Its potential belongs to this actual residual pair. -/
inductive View where
  | leaf
  | left (rest : Stacks)
  | right (rest : Stacks)

namespace View

noncomputable def leftTree {α : Type} (weight : α → ℝ) (l : LabelledTree α) : View → Tree
  | .leaf => .nil
  | .left rest => rest.tree
  | .right _ => rebuild weight l

noncomputable def rightTree {α : Type} (weight : α → ℝ) (r : LabelledTree α) : View → Tree
  | .leaf => .nil
  | .left _ => rebuild weight r
  | .right rest => rest.tree

def potential : View → Nat
  | .leaf => 0
  | .left rest | .right rest => rest.potential

def Valid {α : Type} (weight : α → ℝ) (l r : LabelledTree α) : View → Prop
  | .leaf => l = .nil ∧ r = .nil
  | .left rest => LeftHeavy weight l r ∧ l ≠ .nil ∧
      rest.Represents weight (rebuild weight) (extract weight l).context
  | .right rest => ¬ LeftHeavy weight l r ∧ r ≠ .nil ∧
      rest.Represents weight (rebuild weight) (extract weight r).context

end View
end RotationBST.HeavyPath.Recursive.Exposure
