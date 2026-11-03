module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs
public import RotationBST.Structures.SplitTree.Multiway.Join.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Attach a taller left sibling, retaining the maximum finger and remainder. -/
def maximumJoinOpenCost : Nat → Multiway → Multiway → Nat
  | 0, _, _ => 0
  | _ + 1, .nil, _ => 0
  | d + 1, .two _ b, r => 1 + maximumJoinOpenCost d b r
  | d + 1, .three _ _ c, r => 2 + maximumJoinOpenCost d c r
  | d + 1, .four _ _ _ e, r =>
      match (Join.joinRight d e r).1 with
      | .stay _ => 3 + maximumJoinOpenCost d e r
      | .rise _ _ => 3 + maximumJoinOpenCost d e r + 1

/-- Cost of the same join without a further enclosing separator. -/
def maximumJoinViewCost : Nat → Multiway → Multiway → Nat
  | 0, _, _ => 0
  | _ + 1, .nil, _ => 0
  | d + 1, .two _ b, r => maximumJoinOpenCost d b r
  | d + 1, .three _ _ c, r => 1 + maximumJoinOpenCost d c r
  | d + 1, .four _ _ _ e, r => 1 + maximumJoinOpenCost d e r

/-- Join a shortened maximum interval to its taller left sibling. -/
def attachLeft (focusHeight siblingHeight : Nat) (focus sibling : Multiway) : Join.Result :=
  let result := Join.finish siblingHeight (Join.joinRight (siblingHeight - focusHeight) sibling focus)
  { result with cost := maximumJoinViewCost (siblingHeight - focusHeight) sibling focus }

end RotationBST.Geometric.Split.Multiway.Finger
