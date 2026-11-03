module

public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Partition

/-- A multiway subtree with its computed height. -/
structure Piece where
  tree : Multiway
  height : Nat
  deriving DecidableEq, Repr

def Piece.Valid (p : Piece) : Prop := Balanced p.height p.tree

/-- The two remaining intervals after exposing and removing the split key. -/
structure Cut where
  left : Piece
  right : Piece
  cost : Nat
  deriving DecidableEq, Repr

def Cut.Valid (cut : Cut) : Prop := cut.left.Valid ∧ cut.right.Valid

def Cut.binary (cut : Cut) : Tree := .node cut.left.tree.binary cut.right.tree.binary

/-- Binary root decomposition. Each resulting piece is itself balanced, although
its height need not equal the other piece's height. -/
def children (h : Nat) : Multiway → Piece × Piece
  | .nil => (⟨.nil, 0⟩, ⟨.nil, 0⟩)
  | .two a b => (⟨a, h - 1⟩, ⟨b, h - 1⟩)
  | .three a b c => (⟨a, h - 1⟩, ⟨.two b c, h⟩)
  | .four a b c d => (⟨.two a b, h⟩, ⟨.two c d, h⟩)

def afterLeft (cut : Cut) (right : Piece) : Cut :=
  let joined := Join.compact cut.right.height right.height cut.right.tree right.tree
  ⟨cut.left, ⟨joined.tree, joined.height⟩, cut.cost + 1 + joined.cost⟩

def afterRight (left : Piece) (cut : Cut) : Cut :=
  let joined := Join.compact left.height cut.left.height left.tree cut.left.tree
  ⟨⟨joined.tree, joined.height⟩, cut.right, cut.cost + 1 + joined.cost⟩

/-- Rank-based splitting, rebuilding both remaining intervals by balanced joins.
Fuel counts keys, since binary decomposition can keep the multiway height. -/
def cutAux : Nat → Nat → Multiway → Nat → Cut
  | 0, _, _, _ => ⟨⟨.nil, 0⟩, ⟨.nil, 0⟩, 0⟩
  | fuel + 1, h, t, rank =>
      let (left, right) := children h t
      if rank < left.tree.size then
        afterLeft (cutAux fuel left.height left.tree rank) right
      else if rank = left.tree.size then ⟨left, right, 0⟩
      else afterRight left (cutAux fuel right.height right.tree (rank - left.tree.size - 1))

/-- Split at an existing rank, preserving balanced multiway outputs. -/
def run (height : Nat) (t : Multiway) (rank : Nat) : Cut := cutAux (t.size + 1) height t rank

end RotationBST.Arboral.Split.Multiway.Partition
