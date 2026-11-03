module

public import RotationBST.Algorithms.Simulation.LastTouch.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace RotationBST.Geometric

/-- Maximum last-touch priority in the half-open key interval. Bottom means
that every key there is untouched (or the interval is empty). -/
def supernodePriority (P : Finset Point) (lo hi : Nat) : WithBot Nat :=
  (Finset.Ico lo hi).sup (lastTouch P)

/-- The equal-priority keys forming the root supernode of an interval. This
uses only recorded history, with no tie-breaking or future priorities. -/
def supernodeKeys (P : Finset Point) (lo hi : Nat) : Finset Nat :=
  (Finset.Ico lo hi).filter fun key => lastTouch P key = supernodePriority P lo hi

/-- Between a supernode boundary and a key, no other key of that supernode
occurs. Other equal-priority branches are not incorrectly treated as ancestors. -/
def SupernodeGap (P : Finset Point) (lo hi boundary key : Nat) : Prop :=
  boundary ∈ supernodeKeys P lo hi ∧ lo ≤ key ∧ key < hi ∧ boundary ≠ key ∧
    ∀ y, min boundary key ≤ y → y ≤ max boundary key → y ≠ boundary →
      y ∉ supernodeKeys P lo hi

end RotationBST.Geometric
