module

public import RotationBST.Algorithms.MultipleTrees.Selection.Definitions.Abstract
public import RotationBST.Models.Labelled.Search.Definitions.Abstract
public import RotationBST.Structures.WeightedSearch.Definitions.Abstract

@[expose] public section
namespace RotationBST.MultipleTrees

/-- The most frequent successors, rearranged into key order for comparisons. -/
def cacheKeys (n capacity : Nat) (frequency : Nat → Nat) : List Nat :=
  (selected n capacity frequency).mergeSort (· ≤ ·)

/-- A static cache stores actual universe keys. Its shape balances a mixture of
successor frequencies and uniform weight, controlling both hits and misses. -/
def cacheTree (n capacity : Nat) (frequency : Nat → Nat) : LabelledTree Nat :=
  (WeightedSearch.balancedBuild ((cacheKeys n capacity frequency).map frequency)).labelWith
    (cacheKeys n capacity frequency)

end RotationBST.MultipleTrees
