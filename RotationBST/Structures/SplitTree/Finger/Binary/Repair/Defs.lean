module

public import RotationBST.Structures.SplitTree.Finger.Binary.Defs
public import RotationBST.Structures.SplitTree.Multiway.Edges.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Cost of maintaining the minimum-finger comparison tree during first-child
repair. This differs from the cost in the ordinary multiway binary encoding. -/
def repairViewCost : Multiway → Nat
  | .two (.two _ _) (.four _ _ _ _) => 1
  | .three (.two _ _) (.two _ _) _ | .three (.two _ _) (.three _ _ _) _ => 1
  | .three (.two _ _) (.four _ _ _ _) _ => 3
  | .four (.two _ _) (.two _ _) _ _ | .four (.two _ _) (.three _ _ _) _ _ => 1
  | .four (.two _ _) (.four _ _ _ _) _ _ => 3
  | _ => 0

/-- Update the marked multiway state and its minimum-finger representation.
The result count is for the finger BST, not the ordinary binary encoding. -/
def repairView (t : Multiway) : Multiway × Nat := ((t.repairFirst).1, repairViewCost t)

/-- An interval's finger followed by an enclosing separator and larger keys. -/
def openView (t : Multiway) (rest : Tree) : Tree :=
  comb (binaryView t).spine (.node (binaryView t).tail rest)

/-- Repair cost when the interval has an enclosing separator. -/
def repairOpenCost : Multiway → Nat
  | .two (.two _ _) (.two _ _) | .two (.two _ _) (.three _ _ _) => 1
  | .two (.two _ _) (.four _ _ _ _) => 3
  | t => repairViewCost t

end RotationBST.Arboral.Split.Multiway.Finger
