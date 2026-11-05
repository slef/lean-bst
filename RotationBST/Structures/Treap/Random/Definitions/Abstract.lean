module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace RotationBST.Treap.Random

/-- A sampled order contains every universe key exactly once. -/
def IsOrder (s : Finset Nat) (xs : List Nat) : Prop :=
  xs.Nodup ∧ xs.toFinset = s

/-- Expectation over a random priority order on `s`: choose its next key with
probability proportional to its positive weight, remove it, and repeat.
The sampled list runs from lowest to highest priority. This is an explicit
finite distribution; positivity is required by its probability theorems. -/
noncomputable def average (w : Nat → ℝ) (s : Finset Nat) (f : List Nat → ℝ) : ℝ :=
  if s = ∅ then f [] else
    ∑ x ∈ s.attach, w x.1 / (∑ k ∈ s, w k) *
      average w (s.erase x.1) (fun xs => f (x.1 :: xs))
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem x.2

/-- First key of `s` in an order; `none` if the order contains no such key. -/
def firstIn (s : Finset Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if x ∈ s then some x else firstIn s xs

/-- Probability that `a` has minimum priority in `s`, when priorities are
sampled over the whole universe `u`. -/
noncomputable def firstProbability (w : Nat → ℝ) (u s : Finset Nat) (a : Nat) : ℝ :=
  average w u (fun xs => if firstIn s xs = some a then 1 else 0)

end RotationBST.Treap.Random
