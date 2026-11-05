module

public import RotationBST.Bounds.LazyFinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.LazyFinger

/-- Repeat an alternating pair. A long block has a two-key working set. -/
def pairBlock (x y : Nat) : Nat → List Nat
  | 0 => []
  | rounds + 1 => x :: y :: pairBlock x y rounds

/-- Concatenate alternating blocks for an explicit list of ordered pairs. -/
def pairBlocks (pairs : List (Nat × Nat)) (rounds : Nat) : List Nat :=
  pairs.flatMap fun pair => pairBlock pair.1 pair.2 rounds

/-- All ordered pairs, each occurring in one long alternating block. -/
def pairSequence (n rounds : Nat) : List Nat :=
  pairBlocks ((List.range n).flatMap fun x => (List.range n).map fun y => (x, y)) rounds

/-- All-pairs blocks followed by a repeated key, giving any prescribed length.
The padding key is valid when the universe is nonempty. -/
def pairSequenceAtLength (n m : Nat) : List Nat :=
  pairSequence n (m / (2 * n * n)) ++ List.replicate (m % (2 * n * n)) 0

end RotationBST.LazyFinger
