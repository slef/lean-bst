module

public import RotationBST.Arboral.Definitions.Abstract

@[expose] public section
namespace RotationBST.Arboral

/-- An online geometric algorithm sees only the old point set and the current
request. It must complete the current row without changing past rows. -/
structure OnlineAlgorithm (n : Nat) where
  step : Nat → Nat → Finset Point → Finset Nat
  correct : ∀ time request P, History n time P → ASS P → request < n →
    Completion n time request P (step time request P)

/-- Run from a supplied history, numbering new rows consecutively. -/
def fill (step : Nat → Nat → Finset Point → Finset Nat) :
    Nat → Finset Point → List Nat → Finset Point
  | _, P, [] => P
  | time, P, x :: xs => fill step (time + 1) (P ∪ row time (step time x P)) xs

/-- Charge exactly one unit for every point added, including each request. -/
def rowCost (step : Nat → Nat → Finset Point → Finset Nat) :
    Nat → Finset Point → List Nat → Nat
  | _, _, [] => 0
  | time, P, x :: xs => (step time x P).card +
      rowCost step (time + 1) (P ∪ row time (step time x P)) xs

/-- The access-sequence point set, starting at the supplied time. -/
def requestsAt : Nat → List Nat → Finset Point
  | _, [] => ∅
  | time, x :: xs => insert (x, time) (requestsAt (time + 1) xs)

end RotationBST.Arboral
