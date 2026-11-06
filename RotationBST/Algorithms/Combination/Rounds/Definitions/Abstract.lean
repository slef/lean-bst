module

public import RotationBST.Algorithms.Combination.Controller.Definitions.Abstract
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
namespace RotationBST.Combo.Rounds

/-- Request positions, not key values: equal requests at different indices are
charged separately. `stop` is exclusive. -/
structure Span where
  side : Bool
  start : Nat
  stop : Nat
  deriving DecidableEq

def Span.Contains (span : Span) (index : Nat) : Prop := span.start ≤ index ∧ index < span.stop

/-- Proof accounting for switch positions in the actual executable controller.
A failed request ends the prefix, exactly as in `Controller.run`. -/
def cuts {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat) :
    Controller.State σ → Nat → List Nat → List Nat
  | _, _, [] => []
  | s, offset, x :: xs =>
      let next := Controller.serve worker budget restore s x
      if next.done then
        let rest := cuts worker budget restore next.state (offset + 1) xs
        if next.switched then offset :: rest else rest
      else []

/-- Consecutive rounds share at most their interrupted request. The closing
round includes that index even if its budget was already zero, which is a
conservative coverage convention; no extra worker instruction is inferred. -/
def partition (side : Bool) (start stop : Nat) : List Nat → List Span
  | [] => [⟨side, start, stop⟩]
  | boundary :: rest => ⟨side, start, boundary + 1⟩ :: partition (!side) boundary stop rest

/-- Round coverage of an executed input prefix. The list is a proof witness;
it is not stored by the online controller. -/
def spans {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) : List Span :=
  partition s.side offset (offset + xs.length) (cuts worker budget restore s offset xs)

/-- Earlier and later rounds of the same worker have disjoint request ranges. -/
def Separated (rounds : List Span) : Prop :=
  rounds.Pairwise fun a b => a.side = b.side → a.stop ≤ b.start

def count (side : Bool) (rounds : List Span) : Nat := (rounds.filter fun span => span.side == side).length

/-- The original sequence's amortized charges over this contiguous span. -/
def Span.charge (weights : Nat → ℝ) (span : Span) : ℝ :=
  ∑ i ∈ Finset.Ico span.start span.stop, weights i

def charge (selected : Bool) (weights : Nat → ℝ) (rounds : List Span) : ℝ :=
  ((rounds.filter fun span => span.side == selected).map (Span.charge weights)).sum

end RotationBST.Combo.Rounds
