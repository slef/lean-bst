module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

/-- Group the retained siblings of a last-child frame into one balanced tree. -/
def maximumFrameSibling (h : Nat) : Frame → Multiway.Partition.Piece
  | .twoRight b => ⟨b, h⟩
  | .threeLast b c => ⟨.two b c, h + 1⟩
  | .fourLast b c d => ⟨.three b c d, h + 1⟩
  | _ => ⟨.nil, 0⟩

/-- The ordinary ternary encoding needs one regrouping rotation. -/
def maximumFrameClosedCost : Frame → Nat
  | .fourLast _ _ _ => 1
  | _ => 0

/-- Repair one ancestor whose focused last child has lost height. -/
def maximumRepairFrame (expected actual : Nat) (focus : Multiway) (frame : Frame) : Multiway.Join.Result :=
  let sibling := maximumFrameSibling expected frame
  let result := attachLeft actual sibling.height focus sibling.tree
  { result with cost := maximumFrameClosedCost frame + result.cost }

/-- Regroup the sibling separators before an enclosing remainder. -/
def maximumFrameGroupingCost : Frame → Nat
  | .threeLast _ _ => 1
  | .fourLast _ _ _ => 2
  | _ => 0

def maximumRepairFrameOpenCost (expected actual : Nat) (focus : Multiway) (frame : Frame) : Nat :=
  let sibling := maximumFrameSibling expected frame
  maximumFrameGroupingCost frame + maximumJoinOpenCost (sibling.height - actual) sibling.tree focus

end RotationBST.Arboral.Split.Multiway.Finger
