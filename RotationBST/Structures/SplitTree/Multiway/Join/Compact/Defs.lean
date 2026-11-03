module

public import RotationBST.Structures.SplitTree.Multiway.Join.Defs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Join

/-- Number of separator keys in the root node. -/
def rootKeys : Multiway → Nat
  | .nil => 0
  | .two _ _ => 1
  | .three _ _ _ => 2
  | .four _ _ _ _ => 3

/-- Join with root absorption: two minimal roots of equal height combine into
one full root without changing the binary shape or increasing the height. -/
def compact (hl hr : Nat) (l r : Multiway) : Result :=
  if hl = hr then
    match l, r with
    | .two a b, .two c d => ⟨.four a b c d, hl, 0⟩
    | _, _ => run hl hr l r
  else run hl hr l r

end RotationBST.SplitTree.Multiway.Join
