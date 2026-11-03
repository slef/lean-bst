module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs
public import RotationBST.Structures.SplitTree.Finger.Partition.Defs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded

/-- Output intervals before restoring the shared-root height invariant. -/
inductive Fragment where
  | minimum (piece : Multiway.Partition.Piece)
  | maximum (piece : Multiway.Partition.Piece)
  | shared (state : State)
  deriving DecidableEq, Repr

def Fragment.tree : Fragment → Tree
  | .minimum p => (binaryView p.tree).tree
  | .maximum p => (maximumView p.tree).tree
  | .shared s => s.tree

/-- Multiway-node reserve, counting a shared separator as one node. -/
def Fragment.nodes : Fragment → Nat
  | .minimum p | .maximum p => p.tree.nodes
  | .shared s => s.left.tree.nodes + s.right.tree.nodes + 1

/-- Each stored piece is balanced; shared-root height balance is not asserted. -/
def Fragment.Valid : Fragment → Prop
  | .minimum p | .maximum p => p.Valid
  | .shared s => s.left.Valid ∧ s.right.Valid

structure Exposure where
  left : Fragment
  right : Fragment
  cost : Nat
  deriving DecidableEq, Repr

def Exposure.tree (result : Exposure) : Tree := .node result.left.tree result.right.tree

/-- Split the selected side and rotate the target above the old separator.
The opposite side retains its original finger view. -/
def expose (state : State) (rank : Nat) : Exposure :=
  if rank < state.left.tree.size then
    let cut := splitFromMinimum state.left.tree rank
    ⟨.minimum cut.left, .shared ⟨cut.right, state.right⟩, cut.cost + 1⟩
  else if rank = state.left.tree.size then
    ⟨.minimum state.left, .maximum state.right, 0⟩
  else
    let cut := splitFromMaximum state.right.tree (state.size - 1 - rank)
    ⟨.shared ⟨state.left, cut.left⟩, .maximum cut.right, cut.cost + 1⟩

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded
