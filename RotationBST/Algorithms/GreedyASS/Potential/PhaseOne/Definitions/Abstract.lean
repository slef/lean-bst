module

public import RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- Current blue candidate for an arbitrary ordered cut, including the
intermediate cuts of an LCA-routed split/merge plan. -/
def rootBlue : List Component → Nat → Nat
  | [], _ => 0
  | c :: cs, x => if c.Contains x then Distance.toRoot c x + 1 else rootBlue cs x

/-- During Phase I the geometry and old historical maximum stay fixed.
Only the current forest's blue candidate changes. -/
def select (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) (b : Nat) : WithTop Nat :=
  if ¬ Active P q then WithTop.some 0
  else if External P q then
    if LatestRow P q.2 then b else min (green t lo P q.1) (WithTop.some b)
  else if Glancing P q then
    min (red t lo P q) (WithTop.some (max (purple t lo searches q.2 q.1) b))
  else red t lo P q

def valueAt (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (q : Point) : WithTop Nat :=
  select t lo searches P q (rootBlue roots q.1)

def itemAt (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (x : Nat) : WithTop Nat :=
  match latest P x with
  | none => WithTop.some 0
  | some stamp => valueAt t lo searches P roots (x, stamp)

def amountAt (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (x : Nat) : Nat := (itemAt t lo searches P roots x).untopD 0

def totalAt (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (domain : Finset Nat) : Nat :=
  ∑ x ∈ domain, amountAt t lo searches P roots x

/-- Only an external point not capped by green, or a glancing point not
capped by red, can gain when its blue candidate rises. -/
def Sensitive (t : Tree) (lo : Nat) (P : Finset Point) (q : Point) (b : Nat) : Prop :=
  (External P q ∧ (LatestRow P q.2 ∨ WithTop.some b < green t lo P q.1)) ∨
    (Glancing P q ∧ WithTop.some b < red t lo P q)

instance (t : Tree) (lo : Nat) (P : Finset Point) (q : Point) (b : Nat) :
    Decidable (Sensitive t lo P q b) :=
  inferInstanceAs (Decidable ((_ ∧ (_ ∨ _)) ∨ (_ ∧ _)))

/-- Actual active columns whose selected potential can increase in a merge
from this component. Historical maxima can only reduce this charged set. -/
def chargedKeys (t : Tree) (lo : Nat) (P : Finset Point) (c : Component) : Finset Nat :=
  (P.filter fun q => Active P q ∧ c.Contains q.1 ∧
    Sensitive t lo P q (Distance.toRoot c q.1 + 1)).image Prod.fst

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
