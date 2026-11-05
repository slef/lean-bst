module

public import RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace RotationBST.LazyFinger

/-- Directed adjacent-pair frequency, including the supplied initial key. -/
def frequency : Nat → List Nat → Nat → Nat → Nat
  | _, [], _, _ => 0
  | p, x :: xs, a, b => (if a = p ∧ b = x then 1 else 0) + frequency x xs a b

/-- Boundary traffic computed from a finite directed frequency matrix. -/
def frequencyToll (n : Nat) (f : Nat → Nat → Nat) (lo hi : Nat) : Nat :=
  ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, f a b * cut lo hi a b

end RotationBST.LazyFinger
