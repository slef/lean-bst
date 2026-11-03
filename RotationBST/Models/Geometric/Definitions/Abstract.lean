module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset

@[expose] public section

/-! The geometric view of BST executions (Demaine, Harmon, Iacono, Kane, and
Pătraşcu, 2009): a BST execution touching key `x` at time `t` is the point
`(x, t)`, and a point set is realizable exactly when it is arborally satisfied.
The executable GreedyASS sweep is in `Algorithms/GreedyASS/Algorithm/Abstract`. -/
namespace RotationBST.Arboral

/-- A key and a time, both numbered from zero. -/
abbrev Point := Nat × Nat

/-- The closed axis-aligned rectangle with opposite corners `a` and `b`. -/
def Rectangle (a b p : Point) : Prop :=
  min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
  min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2

/-- Arboral satisfaction: every nondegenerate rectangle spanned by two points
contains a third point, possibly on its boundary. -/
def ASS (P : Finset Point) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a.1 ≠ b.1 → a.2 ≠ b.2 →
    ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ Rectangle a b p

/-- Put a finite set of keys on one time row. -/
def row (time : Nat) (keys : Finset Nat) : Finset Point :=
  keys.image fun x => (x, time)

/-- A history over `n` keys, strictly before the next time `time`. -/
def History (n time : Nat) (P : Finset Point) : Prop :=
  ∀ p ∈ P, p.1 < n ∧ p.2 < time

/-- A legal online extension: include the request, use only valid keys, and
satisfy all rectangles after adding points on this row. -/
def Completion (n time request : Nat) (P : Finset Point) (keys : Finset Nat) : Prop :=
  request ∈ keys ∧ keys ⊆ Finset.range n ∧ ASS (P ∪ row time keys)

/-- A minimum-cardinality legal extension of the current row. This specifies
the greedy geometric algorithm independently of its implementation. -/
def GreedyRow (n time request : Nat) (P : Finset Point) (keys : Finset Nat) : Prop :=
  Completion n time request P keys ∧
    ∀ other, Completion n time request P other → keys.card ≤ other.card

instance (a b p : Point) : Decidable (Rectangle a b p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (P : Finset Point) : Decidable (ASS P) :=
  inferInstanceAs (Decidable (∀ a ∈ P, ∀ b ∈ P, _ → _ → ∃ p ∈ P, _ ∧ _ ∧ _))

instance (n time request : Nat) (P : Finset Point) (keys : Finset Nat) :
    Decidable (Completion n time request P keys) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An offline geometric solution includes all requests and is arborally
satisfied. Its cost is `points.card`; the initial BST convention is separate. -/
structure Solution (requests : Finset Point) where
  points : Finset Point
  contains : requests ⊆ points
  satisfied : ASS points

end RotationBST.Arboral
