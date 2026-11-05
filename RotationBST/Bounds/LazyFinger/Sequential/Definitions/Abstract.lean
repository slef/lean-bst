module

public import RotationBST.Bounds.LazyFinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.LazyFinger

/-- Full ordered scans of the key universe, repeated `rounds` times. -/
def scans (n : Nat) : Nat → List Nat
  | 0 => []
  | rounds + 1 => List.range n ++ scans n rounds

/-- Ordered scans stopped at an exact request count, including a partial last scan. -/
def scanPrefix (n length : Nat) : List Nat :=
  scans n (length / n) ++ List.range (length % n)

end RotationBST.LazyFinger
