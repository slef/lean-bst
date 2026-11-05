module

public import RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized
open Reference

/-- Reference edges traversed between consecutive requests. The first
request has no predecessor and contributes no edges. -/
def edgeCost (t : Tree) (lo : Nat) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: xs => Transitions.edges t lo x y + edgeCost t lo (y :: xs)

/-- Node-counted lazy-finger benchmark on a leaf-oriented reference tree,
with one unit for the first request and no initial root traversal. -/
def referenceCost (t : Tree) (lo : Nat) (xs : List Nat) : Nat :=
  xs.length + edgeCost t lo xs

/-- Potential after all rows of the history have been completed. Virgin
lifetimes are evaluated in the last searched forest after its access. -/
noncomputable def potential (t : Tree) (lo : Nat) (xs : List Nat) : Nat :=
  totalAmount t lo xs (Virgin.points xs) (Finset.range (lo + leaves t)) +
    match xs.getLast? with
    | none => 0
    | some last => Virgin.before t lo xs last

end RotationBST.Geometric.GreedyASS.Potential.Amortized
