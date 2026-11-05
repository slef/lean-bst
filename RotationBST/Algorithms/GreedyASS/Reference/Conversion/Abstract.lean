module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Reference.Conversion.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Conversion.Results
open Potential.Amortized

theorem population (t : Tree) (nonempty : 0 < t.size) : leaves (convert t) = t.size :=
  Conversion.population t nonempty

theorem depth (t : Tree) (lo x : Nat) (valid : x < t.size) :
    Distance.depth (convert t) lo (lo + x) ≤ 2 * Tree.depth t x + 2 :=
  Conversion.depth t lo x valid

theorem distance (t : Tree) (lo x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    Transitions.edges (convert t) lo (lo + x) (lo + y) ≤ 2 * LazyFinger.distance t x y + 4 :=
  Conversion.distance t lo x y hx hy

theorem cost_from (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    referenceCost (convert t) 0 xs ≤ 5 * LazyFinger.costFrom t p xs :=
  Conversion.cost_from t p xs hp valid

theorem cost (t : Tree) (xs : List Nat) (nonempty : 0 < t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    referenceCost (convert t) 0 xs ≤ 5 * LazyFinger.cost t xs :=
  Conversion.cost t xs nonempty valid

end RotationBST.Geometric.GreedyASS.Reference.Conversion.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Reference.Conversion.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Reference.Conversion.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Conversion.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Amortized.Definitions.Abstract]
