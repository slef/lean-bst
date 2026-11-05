module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work
open Cslib.Algorithms.Lean

/-- Unit-cost RAM accounting. Scalar arithmetic/comparison, indexed array reads
and updates, amortized append, and node allocation cost one. Control and list
construction are charged by the traversals below. Values are mathematical
naturals; this is not a bit-complexity or compiled-Lean runtime claim.

As with `TimeM`, primitive cost annotations are part of the model. Algorithm
loops use counted recursion; library allocation and traversal primitives receive
explicit length-dependent charges. -/
abbrev Computation (α : Type) := TimeM Nat α

/-- A primitive or fixed straight-line block with its explicit charge. -/
def charge {α : Type} (steps : Nat) (value : α) : Computation α := ⟨value, steps⟩

/-- Count every callback and list traversal step. -/
def mapList {α β : Type} (f : α → Computation β) : List α → Computation (List β)
  | [] => charge 1 []
  | x :: xs => do
      let y ← f x
      let ys ← mapList f xs
      charge 1 (y :: ys)

/-- Explicit finite-array construction: enumerate indices, evaluate the
callbacks once, and convert the resulting list to an array. -/
def arrayOfFn {α : Type} (n : Nat) (f : Fin n → Computation α) : Computation (Array α) := do
  let indices ← charge (n + 1) (List.finRange n)
  let values ← mapList f indices
  charge (n + 1) values.toArray

/-- Allocate and initialize a constant array. -/
def replicate {α : Type} (n : Nat) (value : α) : Computation (Array α) :=
  charge (n + 1) (Array.replicate n value)

end RotationBST.OptimalLazyFinger.Work
