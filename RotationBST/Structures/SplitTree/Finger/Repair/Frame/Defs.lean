module

public import RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs
public import RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- Group the retained siblings of a first-child frame into one balanced tree. -/
def frameSibling (h : Nat) : Frame → Multiway.Partition.Piece
  | .twoLeft b => ⟨b, h⟩
  | .threeFirst b c => ⟨.two b c, h + 1⟩
  | .fourFirst b c d => ⟨.three b c d, h + 1⟩
  | _ => ⟨.nil, 0⟩

/-- Repair one ancestor whose focused first child has lost height. -/
def repairFrame (expected actual : Nat) (focus : Multiway) (frame : Frame) : Multiway.Join.Result :=
  let sibling := frameSibling expected frame
  attachRight actual sibling.height focus sibling.tree

/-- Regroup the sibling separators before an enclosing remainder. -/
def frameGroupingCost : Frame → Nat
  | .threeFirst _ _ => 1
  | .fourFirst _ _ _ => 2
  | _ => 0

def repairFrameOpenCost (expected actual : Nat) (focus : Multiway) (frame : Frame) : Nat :=
  let sibling := frameSibling expected frame
  frameGroupingCost frame + joinOpenCost (sibling.height - actual) focus sibling.tree

end RotationBST.Geometric.Split.Multiway.Finger
