module

public import RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.ConditionalEntropy

/-- Total outgoing transition frequency on the finite key universe. -/
def rowTotal (n : Nat) (f : Nat → Nat → Nat) (a : Nat) : Nat :=
  ∑ b ∈ Finset.range n, f a b

/-- Empirical conditional information, multiplied by the sequence length.
Zero-frequency terms contribute zero. Outgoing row totals are used so that the
finite sequence's endpoint convention is explicit. -/
noncomputable def information (n : Nat) (f : Nat → Nat → Nat) : ℝ :=
  ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
    (f a b : ℝ) * Real.logb 2 ((rowTotal n f a : ℝ) / (f a b : ℝ))

/-- Conditional information of the directed transitions, including the supplied
predecessor of the first request. It is not implicitly taken to be a tree root. -/
noncomputable def sequenceInformation (n p : Nat) (xs : List Nat) : ℝ :=
  information n (LazyFinger.frequency p xs)

/-- Conditional information using only adjacent requests, without an external
predecessor. Empty and singleton request sequences have no transitions. -/
noncomputable def adjacentInformation (n : Nat) : List Nat → ℝ
  | [] => 0
  | p :: xs => sequenceInformation n p xs

/-- The average empirical conditional entropy; empty sequences are totalized. -/
noncomputable def entropy (n p : Nat) (xs : List Nat) : ℝ :=
  sequenceInformation n p xs / xs.length

/-- Request-normalized conditional benchmark, so deterministic transitions do
not imply a zero service cost. -/
noncomputable def cost (n p : Nat) (xs : List Nat) : ℝ :=
  xs.length + sequenceInformation n p xs

/-- Every next request is determined by the previous key. -/
def Follows (next : Nat → Nat) : Nat → List Nat → Prop
  | _, [] => True
  | p, x :: xs => next p = x ∧ Follows next x xs

/-- Repeat a finite period, preserving all transitions at period boundaries. -/
def repeatPeriod (period : List Nat) : Nat → List Nat
  | 0 => []
  | rounds + 1 => period ++ repeatPeriod period rounds

/-- Sum any fixed charge over the actual directed transitions of a sequence. -/
noncomputable def transitionSum (charge : Nat → Nat → ℝ) : Nat → List Nat → ℝ
  | _, [] => 0
  | p, x :: xs => charge p x + transitionSum charge x xs

end RotationBST.ConditionalEntropy
