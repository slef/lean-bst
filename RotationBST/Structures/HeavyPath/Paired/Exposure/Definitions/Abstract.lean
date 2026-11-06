module

public import RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Stacks
open PopTart LabelledCursor

/-- A path representation permits any valid Chocolate history with the
specified payload fringe. In particular, popping need not recover the shape
chosen by the original sequence of pushes. -/
def Represents {α : Type} (weight : α → ℝ) (payload : LabelledTree α → Tree)
    (cs : List (Frame α)) (p : Stacks) : Prop :=
  p.Valid ∧
  p.lower.decode.fringe = (lowerSlotsWith weight payload cs).reverse ++ [(.nil, 0)] ∧
  p.upper.decode.fringe =
    (upperSlotsWith weight (fun t => (payload t).mirror) cs).reverse ++ [(.nil, 0)]

/-- Enter the selected stack, perform its pop, return to the endpoint,
then descend and rotate to make the exposed ancestor the physical root. -/
def exposeCost {α : Type} (p : Stacks) : Frame α → Nat
  | .left _ _ => p.upper.popCost + 4
  | .right _ _ => p.lower.popCost + 4

end RotationBST.HeavyPath.Paired.Stacks
