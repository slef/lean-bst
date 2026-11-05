module

public import Mathlib.Data.List.Sort

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Rank all keys by decreasing outgoing frequency. Ties retain a valid
nonincreasing order and do not affect the omission bound. -/
def ranking (n : Nat) (frequency : Nat → Nat) : List Nat :=
  (List.range n).mergeSort (fun a b => frequency b ≤ frequency a)

/-- The most frequent successors stored for one predecessor. This list is in
frequency order; an ordered-key representation is built separately. -/
def selected (n capacity : Nat) (frequency : Nat → Nat) : List Nat :=
  (ranking n frequency).take capacity

end RotationBST.MultipleTrees
