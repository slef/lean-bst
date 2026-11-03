module

public import RotationBST.Models.Pointer.Lazy.Rotations.Abstract

@[expose] public section

namespace RotationBST.Pointer.Lazy

/-- Keys in the monochromatic component touching the root, in inorder.
A root of the other color gives the empty component. -/
def componentKeys {α : Type} (color : α → Bool) (wanted : Bool) : LabelledTree α → List α
  | .nil => []
  | .node l x r =>
      if color x = wanted then componentKeys color wanted l ++ x :: componentKeys color wanted r else []

/-- Connectivity in the graph whose edges are the endpoint pairs of a program. -/
inductive Connected {α : Type} (ops : List (α × α)) : α → α → Prop where
  | refl {x : α} : Connected ops x x
  | edge {x y : α} : (x, y) ∈ ops → Connected ops x y
  | symm {x y : α} : Connected ops x y → Connected ops y x
  | trans {x y z : α} : Connected ops x y → Connected ops y z → Connected ops x z

/-- Endpoint occurrences, retaining duplicates so its length is exactly twice
 the program length. -/
def endpointSupport {α : Type} (ops : List (α × α)) : List α :=
  ops.flatMap fun e => [e.1, e.2]

end RotationBST.Pointer.Lazy
