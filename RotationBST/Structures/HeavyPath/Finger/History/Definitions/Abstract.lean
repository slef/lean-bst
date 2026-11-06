module

public import RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History
open Paired LabelledCursor Recursive Recursive.History

/-- Shift each ancestor's weight to the next payload toward the finger.
Payload shapes belong to occurrences, independently of their source labels. -/
def sideSlots {α : Type} (weight : α → ℝ) (boundary : LabelledTree α) (shape : Tree) :
    ℝ → List (Entry α) → List (Tree × ℝ)
  | carry, [] => [(shape, carry + HeavyPath.mass weight boundary)]
  | carry, e :: es => (e.shape, carry + HeavyPath.mass weight (framePayload e.source)) ::
      sideSlots weight boundary shape (weight (frameKey e.source)) es

/-- All physical payload occurrences of an inverted source cursor. -/
structure State (α : Type) where
  ancestors : List (Entry α)
  leftShape : Tree
  rightShape : Tree
  leftCredit : Nat
  rightCredit : Nat
  pair : Pair

def State.potential {α : Type} (s : State α) : Nat :=
  s.pair.potential + s.leftCredit + s.rightCredit + (s.ancestors.map Entry.credit).sum

/-- The whole inverted-cursor invariant. Depth is a consequence, not a field.
Every ancestor payload and both finger children retain their recursive layouts. -/
structure Valid {α : Type} (weight : α → ℝ) (cs : List (Frame α))
    (left : LabelledTree α) (key : α) (right : LabelledTree α) (s : State α) : Prop where
  positive : Positive weight (plug cs (.node left key right))
  context : s.ancestors.map Entry.source = cs
  pair : s.pair.Valid
  leftLayout : Recursive.History.Layout weight left s.leftShape s.leftCredit
  rightLayout : Recursive.History.Layout weight right s.rightShape s.rightCredit
  children : ∀ e ∈ s.ancestors,
    Recursive.History.Layout weight (framePayload e.source) e.shape e.credit
  lower : s.pair.lower.decode.mirror.fringe =
    sideSlots weight left s.leftShape 0 (Recursive.History.lower s.ancestors)
  upper : s.pair.upper.decode.fringe =
    (sideSlots weight right s.rightShape 0 (Recursive.History.upper s.ancestors).reverse).reverse

end RotationBST.HeavyPath.Finger.History
