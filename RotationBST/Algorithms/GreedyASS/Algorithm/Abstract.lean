module

public import RotationBST.Models.Geometric.Definitions.Abstract

@[expose] public section

/-! GreedyASS (Demaine, Harmon, Iacono, Kane, and Pătraşcu, 2009): complete the
current row with the request and the projections of every old point whose
rectangle with the request is empty. Its specification, `GreedyRow`, is part of
the geometric model in `Models/Geometric/Definitions/Abstract`. -/
namespace RotationBST.Arboral

/-- An old point whose rectangle with the new request has no third old point. -/
def Visible (P : Finset Point) (time request : Nat) (q : Point) : Prop :=
  q.1 ≠ request ∧ ∀ p ∈ P, p ≠ q → ¬ Rectangle q (request, time) p

instance (P : Finset Point) (time request : Nat) (q : Point) :
    Decidable (Visible P time request q) :=
  inferInstanceAs (Decidable (_ ∧ ∀ p ∈ P, _ → ¬ _))

/-- The usual GreedyASS sweep: project every old point making an empty
rectangle with the request onto the new row, and include the request itself. -/
def greedySweep (time request : Nat) (P : Finset Point) : Finset Nat :=
  insert request ((P.filter (Visible P time request)).image Prod.fst)

/-- Keep the smaller set, retaining the first in a tie. -/
def smaller (a b : Finset Nat) : Finset Nat :=
  if b.card < a.card then b else a

/-- Enumerate all subsets of the key universe. -/
def subsets : Nat → List (Finset Nat)
  | 0 => [∅]
  | n + 1 => subsets n ++ (subsets n).map (insert n)

/-- An executable exhaustive implementation of the minimum-row rule.
Only geometric point cost is studied here; enumeration time is exponential. -/
def greedy (n time request : Nat) (P : Finset Point) : Finset Nat :=
  ((subsets n).filter fun keys => decide (Completion n time request P keys)).foldl
    smaller (Finset.range n)

end RotationBST.Arboral
