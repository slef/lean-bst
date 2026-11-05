module

public import RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract
public import RotationBST.Structures.PrefixSum.Definitions.Abstract

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Preprocessing
open PrefixSum

/-- A dense square transition table. -/
def Square (t : Table) (n : Nat) : Prop :=
  t.size = n ∧ ∀ a < n, (t[a]?.getD #[]).size = n

/-- Record one directed transition. -/
def increment (t : Table) (a b : Nat) : Table :=
  t.modify a (fun r => r.modify b (fun x => x + 1))

/-- Accumulate adjacent transitions in one pass over the requests. -/
def fill : Table → Nat → List Nat → Table
  | t, _, [] => t
  | t, p, x :: xs => fill (increment t p x) x xs

def frequencies (n p : Nat) (xs : List Nat) : Table :=
  fill (Array.replicate n (Array.replicate n 0)) p xs

/-- Preprocessed transition prefixes, including any virtual initial key in `n`. -/
def prepare (n p : Nat) (xs : List Nat) : Table :=
  let f := frequencies n p xs
  build (get f) n n

/-- Constant-number rectangle queries for traffic crossing `[lo,hi)`. -/
def toll (p : Table) (n lo hi : Nat) : Nat :=
  rectangle p lo hi 0 lo + rectangle p lo hi hi n +
    rectangle p 0 lo lo hi + rectangle p hi n lo hi

end RotationBST.OptimalLazyFinger.Preprocessing
