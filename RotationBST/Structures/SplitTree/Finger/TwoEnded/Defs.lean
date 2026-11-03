module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

/-- One physical nonempty BST with a minimum finger on the left and a maximum
finger on the right of a separating root key. -/
structure State where
  left : Multiway.Partition.Piece
  right : Multiway.Partition.Piece
  deriving DecidableEq, Repr

def State.tree (state : State) : Tree :=
  .node (binaryView state.left.tree).tree (maximumView state.right.tree).tree

def State.size (state : State) : Nat := state.left.tree.size + 1 + state.right.tree.size

/-- Each side is multiway-balanced; the two side sizes differ by at most a
factor of two, allowing for an empty side in the smallest trees. -/
def State.Valid (state : State) : Prop :=
  state.left.Valid ∧ state.right.Valid ∧
    state.left.tree.size ≤ 2 * state.right.tree.size + 1 ∧
    state.right.tree.size ≤ 2 * state.left.tree.size + 1

/-- Establish both fingers around a median root, using the existing balanced
splitter and spine-only conversions. -/
def make (height : Nat) (t : Multiway) : State × Nat :=
  let cut := Multiway.Partition.run height t ((t.size - 1) / 2)
  (⟨cut.left, cut.right⟩, cut.cost + conversionCost cut.left.tree + maximumCost cut.right.tree)

/-- The root comparison chooses the appropriate stored endpoint; a root hit
requires no descent. -/
def chosenDistance (state : State) (rank : Nat) : Nat :=
  if rank < state.left.tree.size then rank
  else if rank = state.left.tree.size then 0
  else state.size - 1 - rank

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
