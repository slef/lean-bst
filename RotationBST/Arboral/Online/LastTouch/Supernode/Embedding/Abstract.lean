module

public import RotationBST.Pointer.Lazy.Skeleton.Abstract

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Pointer.Lazy

/-- Realize a supernode's key-only shape, placing an untouched subtree in each
external gap. Gap indices count supernode keys, not keys inside gap subtrees. -/
def withGaps : Tree → (Nat → Tree) → Nat → Skeleton
  | .nil, gaps, offset => .hole (gaps offset)
  | .node l r, gaps, offset =>
      .node (withGaps l gaps offset) (withGaps r gaps (offset + l.size + 1))

/-- Number of ordinary BST keys contained in a consecutive run of gaps. -/
def gapWeight (gaps : Nat → Tree) : Nat → Nat → Nat
  | _, 0 => 0
  | offset, count + 1 => (gaps offset).size + gapWeight gaps (offset + 1) count

/-- Full-tree rank of a supernode key, accounting for all preceding gaps. -/
def keyRank (gaps : Nat → Tree) (offset rank : Nat) : Nat :=
  rank + gapWeight gaps offset (rank + 1)

end RotationBST.Arboral.Online.Supernode
