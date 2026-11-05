module

public import RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Algorithm.Abstract
public import Mathlib.Order.WithBot
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

/-- Columns of actual active external points, not all previously accessed keys. -/
def externalKeys (P : Finset Point) : Finset Nat :=
  (P.filter fun q => External P q).image Prod.fst

def leftExternal (P : Finset Point) (x : Nat) : Option Nat :=
  greatest ((externalKeys P).filter fun y => y < x)

def rightExternal (P : Finset Point) (x : Nat) : Option Nat :=
  least ((externalKeys P).filter fun y => x < y)

/-- Red is finite precisely when both same-row neighbors exist. Infinity
marks an undefined candidate; active nonexternal points have both neighbors. -/
def red (t : Tree) (lo : Nat) (P : Finset Point) (q : Point) : WithTop Nat :=
  match leftNeighbor P q, rightNeighbor P q with
  | some a, some b => (Distance.toLCA t lo q.1 a b : Nat)
  | _, _ => ⊤

/-- Missing either external neighbor gives the paper's infinite green value. -/
def green (t : Tree) (lo : Nat) (P : Finset Point) (x : Nat) : WithTop Nat :=
  match leftExternal P x, rightExternal P x with
  | some a, some b => (Distance.toLCA t lo x a b + 1 : Nat)
  | _, _ => ⊤

/-- Compute the blue value in the actual forest by following the search path
until it separates from the item's path. Distances count nodes, then add one. -/
def blue : Tree → Nat → Nat → Nat → Nat
  | .nil, _, _, _ => 2
  | .node l r, lo, searched, x =>
      if searched < lo + leaves l then
        if x < lo + leaves l then blue l lo searched x
        else Distance.depth r (lo + leaves l) x + 2
      else
        if x < lo + leaves l then Distance.depth l lo x + 2
        else blue r (lo + leaves l) searched x

/-- Empty histories have no current forest contribution. -/
def currentBlue (t : Tree) (lo : Nat) (searches : List Nat) (x : Nat) : Nat :=
  match searches.getLast? with
  | none => 0
  | some searched => blue t lo searched x

/-- Inclusive maximum from the most recent access row through the current
search. Row zero corresponds to the first entry in `searches`. -/
def purple (t : Tree) (lo : Nat) (searches : List Nat) (stamp x : Nat) : Nat :=
  (searches.drop stamp).toFinset.sup fun searched => blue t lo searched x

inductive Color where
  | red | green | blue | purple
  deriving DecidableEq, Repr

/-- Snapshot coloring. Appending the current search while keeping the old
point set computes the paper's intermediate Phase I colors. Top-corner
status uses the latest row of that point set, not the search-history length. -/
def color (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) : Option Color :=
  if ¬ Active P q then none
  else if External P q then
    if LatestRow P q.2 then some .blue
    else if green t lo P q.1 ≤ (currentBlue t lo searches q.1 : WithTop Nat) then some .green
    else some .blue
  else if Glancing P q then
    if red t lo P q < (purple t lo searches q.2 q.1 : WithTop Nat) then some .red
    else some .purple
  else some .red

/-- The selected item potential, zero for inactive points. -/
def value (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) : WithTop Nat :=
  match color t lo searches P q with
  | none => ((0 : Nat) : WithTop Nat)
  | some .red => red t lo P q
  | some .green => green t lo P q.1
  | some .blue => (currentBlue t lo searches q.1 : Nat)
  | some .purple => (purple t lo searches q.2 q.1 : Nat)

/-- Item-level queries use the actual most recent access in each column.
This also applies to intermediate colors computed from the old point set. -/
def itemColor (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) : Option Color :=
  match latest P x with
  | none => none
  | some stamp => color t lo searches P (x, stamp)

def itemValue (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) : WithTop Nat :=
  match latest P x with
  | none => ((0 : Nat) : WithTop Nat)
  | some stamp => value t lo searches P (x, stamp)

/-- Natural-valued item potential. The selected value is always finite;
the proof interface certifies that this conversion loses no information. -/
def itemAmount (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) : Nat :=
  (itemValue t lo searches P x).untopD 0

def totalAmount (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (keys : Finset Nat) : Nat := ∑ x ∈ keys, itemAmount t lo searches P x

def coloredKeys (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (keys : Finset Nat) (c : Color) : Finset Nat :=
  keys.filter fun x => itemColor t lo searches P x = some c

def unseenKeys (P : Finset Point) (keys : Finset Nat) : Finset Nat :=
  keys.filter fun x => latest P x = none

/-- Count keys with no old color along the actual GreedyASS execution. -/
def firstAccesses : Nat → Finset Point → List Nat → Nat
  | _, _, [] => 0
  | time, P, x :: xs =>
      (unseenKeys P (greedySweep time x P)).card +
        firstAccesses (time + 1) (P ∪ row time (greedySweep time x P)) xs

end RotationBST.Geometric.GreedyASS.Potential
