module

public import RotationBST.Algorithms.GreedyASS.Algorithm.Abstract
public import RotationBST.Models.Geometric.Online.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Barrier

/-- The point at `(key, stamp)` blocks old points strictly to its left:
none of those points is more recent than the barrier. -/
def Left (P : Finset Point) (key stamp : Nat) : Prop :=
  (key, stamp) ∈ P ∧ ∀ p ∈ P, p.1 < key → p.2 ≤ stamp

/-- Symmetric barrier for points strictly to the right. -/
def Right (P : Finset Point) (key stamp : Nat) : Prop :=
  (key, stamp) ∈ P ∧ ∀ p ∈ P, key < p.1 → p.2 ≤ stamp

end RotationBST.Geometric.GreedyASS.Barrier
