module

public import RotationBST.Structures.SplitTree.Finger.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- A binary right spine, with each off-spine subtree attached on the left. -/
def comb : List Tree → Tree → Tree
  | [], tail => tail
  | a :: rest, tail => .node a (comb rest tail)

/-- Comparison-tree view of the minimum finger. The retained subtrees appear
in their original inorder order; only the spine separators are regrouped. -/
structure BinaryView where
  spine : List Tree
  tail : Tree
  deriving DecidableEq, Repr

def BinaryView.tree (v : BinaryView) : Tree := comb v.spine v.tail

def binaryView : Multiway → BinaryView
  | .nil => ⟨[], .nil⟩
  | .two a b => let v := binaryView a; ⟨v.spine ++ [v.tail], b.binary⟩
  | .three a b c => let v := binaryView a; ⟨v.spine ++ [v.tail, b.binary], c.binary⟩
  | .four a b c d => let v := binaryView a; ⟨v.spine ++ [v.tail, b.binary, c.binary], d.binary⟩

/-- Exact rotation count for constructing the minimum-finger comparison tree. -/
def viewCost : Multiway → Nat
  | .nil => 0
  | .two a _ | .three a _ _ => viewCost a + (binaryView a).spine.length
  | .four a _ _ _ => viewCost a + 2 * (binaryView a).spine.length + 1

end RotationBST.Arboral.Split.Multiway.Finger
