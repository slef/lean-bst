module

public import RotationBST.Structures.SplitTree.Finger.Locate.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- Nearest-first ancestors of the maximum external leaf, retaining ordinary
multiway siblings without reflecting their binary encodings. -/
def rightSpine : Multiway → List Frame
  | .nil => []
  | .two a b => rightSpine b ++ [.twoRight a]
  | .three a b c => rightSpine c ++ [.threeLast a b]
  | .four a b c d => rightSpine d ++ [.fourLast a b c]

/-- Locate an interval by distance from its maximum, not by increasing rank. -/
def locateMaximum (t : Multiway) (distance : Nat) : Location :=
  let levels := ascend (rightSpine t) .nil distance
  ⟨plug ((rightSpine t).take levels) .nil, levels, (rightSpine t).drop levels⟩

end RotationBST.Geometric.Split.Multiway.Finger
