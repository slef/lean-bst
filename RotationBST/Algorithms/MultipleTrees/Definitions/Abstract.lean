module

public import RotationBST.Models.LinkedSearch.Definitions.Abstract
public import RotationBST.Algorithms.MultipleTrees.Cache.Definitions.Abstract

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Preprocessing converts a universe key into its local-root address. The
modulus only totalizes out-of-universe inputs; stored and requested keys are valid. -/
def rootAddress (n : Nat) (positive : 0 < n) (x : Nat) : Fin n :=
  ⟨x % n, Nat.mod_lt x positive⟩

/-- The shared fallback contains every universe key with a uniformly balanced
shape. Frequencies are unnecessary for this tree. -/
def fallbackTree (n : Nat) : LabelledTree Nat := cacheTree n n (fun _ => 0)

/-- Preprocess a frequency matrix into local successor caches and one shared
fallback. Only trees and root pointers are stored; the frequency matrix is not
a field of the resulting runtime store. -/
def build (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) :
    LinkedSearch.Store (Fin n) where
  roots p := LinkedSearch.attach (rootAddress n positive) (cacheTree n capacity (frequency p))
  fallback := LinkedSearch.attach (rootAddress n positive) (fallbackTree n)

end RotationBST.MultipleTrees
