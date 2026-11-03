module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! Wilber's interleave quantity (Wilber 1989, in the convention of Demaine,
Harmon, Iacono, and Pătraşcu 2007). A fixed reference BST on the same keys
splits every subtree into a left region (the node and its left subtree) and a
right region; the quantity counts how often consecutive requests inside a
subtree alternate between the two regions, summed over all subtrees.

The lower-bound theorems are in `Bounds/Interleave/Abstract`; Tango's own
vocabulary is in `Algorithms/Tango/Definitions/Abstract`. -/
namespace RotationBST.Wilber

/-- The reference-tree convention of Demaine–Harmon–Iacono–Pătraşcu:
the node itself belongs to its left region. `true` denotes that region. -/
def regions (leftSize size : Nat) (xs : List Nat) : List Bool :=
  (xs.filter (· < size)).map (· ≤ leftSize)

def leftRequests (leftSize : Nat) (xs : List Nat) : List Nat :=
  xs.filter (· < leftSize)

def rightRequests (leftSize : Nat) (xs : List Nat) : List Nat :=
  (xs.filter (leftSize < ·)).map (· - leftSize - 1)

/-- Number of switches between consecutive nonempty region observations. -/
def alternations : List Bool → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: xs => (if a = b then 0 else 1) + alternations (b :: xs)

/-- Wilber's interleave quantity for an arbitrary fixed unlabelled reference
BST. This definition alone does not assert the BST lower-bound theorem. -/
def interleave : Tree → List Nat → Nat
  | .nil, _ => 0
  | .node l r, xs => alternations (regions l.size (l.size + 1 + r.size) xs) +
      interleave l (leftRequests l.size xs) + interleave r (rightRequests l.size xs)

/-- A first observation initializes a preference, and does not count as a switch. -/
def switch (past : List Bool) (next : Bool) : Nat :=
  match past.getLast? with
  | none => 0
  | some previous => if previous = next then 0 else 1

end RotationBST.Wilber
