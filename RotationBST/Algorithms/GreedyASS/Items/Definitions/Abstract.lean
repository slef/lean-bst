module

public import RotationBST.Models.Geometric.Offline.Abstract
public import Mathlib.Data.Finset.Max

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

def greatest (s : Finset Nat) : Option Nat :=
  if h : s.Nonempty then some (s.max' h) else none

def least (s : Finset Nat) : Option Nat :=
  if h : s.Nonempty then some (s.min' h) else none

/-- Access times in one column, without an artificial time for unseen keys. -/
def times (P : Finset Point) (key : Nat) : Finset Nat :=
  (P.filter fun p => p.1 = key).image Prod.snd

/-- Time coordinate of the most recent access, or none for an unseen item. -/
def latest (P : Finset Point) (key : Nat) : Option Nat := greatest (times P key)

/-- Nearest same-row accesses on either side of an active point. -/
def leftNeighbor (P : Finset Point) (q : Point) : Option Nat :=
  greatest ((keysAt P q.2).filter fun x => x < q.1)

def rightNeighbor (P : Finset Point) (q : Point) : Option Nat :=
  least ((keysAt P q.2).filter fun x => q.1 < x)

def Active (P : Finset Point) (q : Point) : Prop :=
  q ∈ P ∧ ∀ p ∈ P, p.1 = q.1 → p.2 ≤ q.2

/-- Whether a row is at least as recent as every point in this snapshot.
This depends on the point set, including during a reference-forest update. -/
def LatestRow (P : Finset Point) (stamp : Nat) : Prop :=
  ∀ p ∈ P, p.2 ≤ stamp

instance (P : Finset Point) (stamp : Nat) : Decidable (LatestRow P stamp) :=
  inferInstanceAs (Decidable (∀ p ∈ P, p.2 ≤ stamp))

def LeftExternal (P : Finset Point) (q : Point) : Prop :=
  Active P q ∧ ∀ p ∈ P, p.2 = q.2 → q.1 ≤ p.1

def RightExternal (P : Finset Point) (q : Point) : Prop :=
  Active P q ∧ ∀ p ∈ P, p.2 = q.2 → p.1 ≤ q.1

def External (P : Finset Point) (q : Point) : Prop :=
  LeftExternal P q ∨ RightExternal P q

def LeftGlancing (P : Finset Point) (q : Point) : Prop :=
  Active P q ∧ ¬ External P q ∧ ∀ p ∈ P, q.2 < p.2 → q.1 < p.1

def RightGlancing (P : Finset Point) (q : Point) : Prop :=
  Active P q ∧ ¬ External P q ∧ ∀ p ∈ P, q.2 < p.2 → p.1 < q.1

def Glancing (P : Finset Point) (q : Point) : Prop :=
  LeftGlancing P q ∨ RightGlancing P q

def Internal (P : Finset Point) (q : Point) : Prop :=
  Active P q ∧ ¬ External P q ∧ ¬ Glancing P q

instance (P : Finset Point) (q : Point) : Decidable (Active P q) :=
  inferInstanceAs (Decidable (_ ∧ ∀ p ∈ P, _ → _))

instance (P : Finset Point) (q : Point) : Decidable (LeftExternal P q) :=
  inferInstanceAs (Decidable (Active P q ∧ ∀ p ∈ P, _ → _))

instance (P : Finset Point) (q : Point) : Decidable (RightExternal P q) :=
  inferInstanceAs (Decidable (Active P q ∧ ∀ p ∈ P, _ → _))

instance (P : Finset Point) (q : Point) : Decidable (External P q) :=
  inferInstanceAs (Decidable (LeftExternal P q ∨ RightExternal P q))

instance (P : Finset Point) (q : Point) : Decidable (LeftGlancing P q) :=
  inferInstanceAs (Decidable (Active P q ∧ ¬ External P q ∧ ∀ p ∈ P, _ → _))

instance (P : Finset Point) (q : Point) : Decidable (RightGlancing P q) :=
  inferInstanceAs (Decidable (Active P q ∧ ¬ External P q ∧ ∀ p ∈ P, _ → _))

instance (P : Finset Point) (q : Point) : Decidable (Glancing P q) :=
  inferInstanceAs (Decidable (LeftGlancing P q ∨ RightGlancing P q))

instance (P : Finset Point) (q : Point) : Decidable (Internal P q) :=
  inferInstanceAs (Decidable (Active P q ∧ ¬ External P q ∧ ¬ Glancing P q))

/-- External items accessed on the new row, the paper's top corners. -/
def corners (P : Finset Point) (time : Nat) (keys : Finset Nat) : Finset Nat :=
  keys.filter fun x => External (P ∪ row time keys) (x, time)

end RotationBST.Geometric.GreedyASS.Items
