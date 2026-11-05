module

public import RotationBST.Models.Rotation.Search.Abstract
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import RotationBST.Models.Multifinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand

/-- Compress all unmarked unary vertices of the rooted Steiner tree. Marked
vertices and branching vertices remain. Insert the original root into `marks`
when a root-anchored hand is required. -/
def compress (marks : Finset Nat) : Tree → Nat → LabelledTree Nat
  | .nil, _ => .nil
  | .node l r, lo =>
      let left := compress marks l lo
      let right := compress marks r (lo + l.size + 1)
      if lo + l.size ∈ marks then .node left (lo + l.size) right
      else match left, right with
        | .nil, _ => right
        | _, .nil => left
        | _, _ => .node left (lo + l.size) right

/-- Number of marked keys actually present in the reference interval. -/
def markedCount (marks : Finset Nat) : Tree → Nat → Nat
  | .nil, _ => 0
  | .node l r, lo =>
      markedCount marks l lo + (if lo + l.size ∈ marks then 1 else 0) +
        markedCount marks r (lo + l.size + 1)

/-- The original root rank. The empty-tree value is only a totalization. -/
def rootRank : Tree → Nat
  | .nil => 0
  | .node l _ => l.size

/-- Actual finger keys, with the original root included as an anchor. Duplicate
fingers create a single mark. -/
def stateMarks {k : Nat} (s : Multifinger.State k) : Finset Nat :=
  insert (rootRank s.tree) (Finset.univ.image s.position)

def ofState {k : Nat} (s : Multifinger.State k) : LabelledTree Nat := compress (stateMarks s) s.tree 0

/-- The keys below the endpoint, in their order on its root-to-key path. -/
def lowerPath (t : Tree) (lo x : Nat) : List Nat := (t.searchPath lo x).filter (· < x)

/-- The keys above the endpoint, in their order on its root-to-key path. -/
def upperPath (t : Tree) (lo x : Nat) : List Nat := (t.searchPath lo x).filter (x < ·)

end RotationBST.FingerHand
