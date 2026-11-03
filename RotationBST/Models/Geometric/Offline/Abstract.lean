module

public import RotationBST.Models.Geometric.Online.Abstract

@[expose] public section
namespace RotationBST.Geometric

/-- The rows strictly preceding `time`. -/
def pastPoints (P : Finset Point) (time : Nat) : Finset Point :=
  P.filter fun p => p.2 < time

/-- The keys touched at a given time. -/
def keysAt (P : Finset Point) (time : Nat) : Finset Nat :=
  (P.filter fun p => p.2 = time).image Prod.fst

/-- A bounded offline geometric execution of the given access sequence.
The entire set may depend on future requests. -/
structure Offline (n : Nat) (xs : List Nat) extends Solution (requestsAt 0 xs) where
  bounded : History n xs.length points

/-- The number of points in the first `time` rows, computed row by row. -/
def scheduleCost (P : Finset Point) : Nat → Nat
  | 0 => 0
  | time + 1 => scheduleCost P time + (keysAt P time).card

end RotationBST.Geometric
