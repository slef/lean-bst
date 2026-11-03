module

public import RotationBST.Structures.SplitTree.Multiway.Context.Abstract
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger
open Context

/-- Nearest-first ancestors of the leftmost external leaf. Each frame retains
its siblings, so the original tree can be reconstructed exactly. -/
def leftSpine : Multiway → List Frame
  | .nil => []
  | .two a b => leftSpine a ++ [.twoLeft b]
  | .three a b c => leftSpine a ++ [.threeFirst b c]
  | .four a b c d => leftSpine a ++ [.fourFirst b c d]

/-- Ascend until the growing leftmost interval contains `rank`. The result is
the number of crossed multiway levels, not a claim about BST rotation cost. -/
def ascend : List Frame → Multiway → Nat → Nat
  | [], _, _ => 0
  | f :: fs, focus, rank =>
      if rank < focus.size then 0 else 1 + ascend fs (f.fill focus) rank

/-- Number of levels needed to locate a containing ancestor from the minimum. -/
def searchLevels (t : Multiway) (rank : Nat) : Nat := ascend (leftSpine t) .nil rank

/-- Reverse the multiway order to obtain the corresponding maximum finger. -/
def mirror : Multiway → Multiway
  | .nil => .nil
  | .two a b => .two (mirror b) (mirror a)
  | .three a b c => .three (mirror c) (mirror b) (mirror a)
  | .four a b c d => .four (mirror d) (mirror c) (mirror b) (mirror a)

/-- Choose the nearer endpoint by rank distance, then ascend from that finger. -/
def nearSearchLevels (t : Multiway) (rank : Nat) : Nat :=
  if rank ≤ t.size - 1 - rank then searchLevels t rank
  else searchLevels (mirror t) (t.size - 1 - rank)

end RotationBST.Geometric.Split.Multiway.Finger
