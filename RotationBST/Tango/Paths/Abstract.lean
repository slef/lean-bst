module

public import RotationBST.Tango.Wilber.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- A component beginning at the current root, and the remaining components. -/
abbrev PathDecomposition := List Nat × List (List Nat)

def PathDecomposition.parts (d : PathDecomposition) : List (List Nat) :=
  if d.1 = [] then d.2 else d.1 :: d.2

/-- Compute the preferred-path partition of the fixed reference tree from past
requests. Each path lists its keys from shallowest to deepest in the reference. -/
def decomposePaths : Tree → Nat → List Nat → PathDecomposition
  | .nil, _, _ => ([], [])
  | .node l r, lo, past =>
      let left := decomposePaths l lo past
      let right := decomposePaths r (lo + l.size + 1) past
      let root := lo + l.size
      match (labels lo root (lo + l.size + 1 + r.size) past).getLast? with
      | none => ([root], left.parts ++ right.parts)
      | some true => (root :: left.1, left.2 ++ right.parts)
      | some false => (root :: right.1, left.parts ++ right.2)

/-- The current preferred paths, with no empty components. -/
def preferredPaths (reference : Tree) (past : List Nat) : List (List Nat) :=
  (decomposePaths reference 0 past).parts

end RotationBST.Tango
