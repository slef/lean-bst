module

public import RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Transitions

inductive Event where
  | split (first : Nat) (left right : Tree)
  | merge (first : Nat) (left right : Tree)
  deriving DecidableEq, Repr

def Event.inverse : Event → Event
  | .split lo l r => .merge lo l r
  | .merge lo l r => .split lo l r

def Event.parent : Event → Component
  | .split lo l r | .merge lo l r => ⟨lo, .node l r⟩

/-- Number of component roots introduced by a local rewrite. Removed
roots may carry credit, so this bounds the increase in virgin-root count. -/
def Event.introduced : Event → Nat
  | .split _ _ _ => 2
  | .merge _ _ _ => 1

def Event.isMerge : Event → Bool
  | .split _ _ _ => false
  | .merge _ _ _ => true

/-- Count merge events for the reserved item-potential budget. -/
def merges (events : List Event) : Nat := events.countP Event.isMerge

/-- Total root introductions along an event trace, counting repeated births. -/
def introductions (events : List Event) : Nat := (events.map Event.introduced).sum

/-- The event's parent must occur in the fixed reference tree. Merely having
adjacent intervals does not make two components siblings in that tree. -/
def Admissible (t : Tree) (lo : Nat) (event : Event) : Prop :=
  ∃ k, Distance.Occurs t lo event.parent k

/-- An ordered partition of the reference leaves by actual subtree roots. -/
structure Cut (t : Tree) (lo : Nat) (roots : List Component) : Prop where
  ordered : roots.Pairwise (fun a b => a.last ≤ b.first)
  occurs : ∀ c ∈ roots, ∃ k, Distance.Occurs t lo c k
  covers : ∀ x, lo ≤ x ∧ x < lo + leaves t → ∃ c ∈ roots, c.Contains x

/-- A local forest rewrite. Reference-tree membership is certified separately
by `Admissible`; the rewrite alone only checks shapes and offsets. -/
inductive Step : List Component → Event → List Component → Prop
  | split (before after : List Component) (lo : Nat) (l r : Tree) :
      Step (before ++ [⟨lo, .node l r⟩] ++ after) (.split lo l r)
        (before ++ [⟨lo, l⟩, ⟨lo + leaves l, r⟩] ++ after)
  | merge (before after : List Component) (lo : Nat) (l r : Tree) :
      Step (before ++ [⟨lo, l⟩, ⟨lo + leaves l, r⟩] ++ after) (.merge lo l r)
        (before ++ [⟨lo, .node l r⟩] ++ after)

inductive Trace : List Component → List Event → List Component → Prop
  | nil (roots : List Component) : Trace roots [] roots
  | cons {a b c : List Component} {event : Event} {events : List Event} :
      Step a event b → Trace b events c → Trace a (event :: events) c

/-- Split the root and continue only along the searched leaf's path. -/
def descend : Tree → Nat → Nat → List Event
  | .nil, _, _ => []
  | .node l r, lo, searched =>
      .split lo l r ::
        if searched < lo + leaves l then descend l lo searched
        else descend r (lo + leaves l) searched

def ascend (t : Tree) (lo searched : Nat) : List Event :=
  (descend t lo searched).reverse.map Event.inverse

/-- Common ancestors need no changes. At the LCA, first merge toward its
root, then split along the new search path. -/
def plan : Tree → Nat → Nat → Nat → List Event
  | .nil, _, _, _ => []
  | .node l r, lo, old, new =>
      if old < lo + leaves l ∧ new < lo + leaves l then plan l lo old new
      else if lo + leaves l ≤ old ∧ lo + leaves l ≤ new then plan r (lo + leaves l) old new
      else ascend (.node l r) lo old ++ descend (.node l r) lo new

/-- Number of reference edges on the leaf-to-leaf path. The paper's
node-counted distance is one larger, even for repeated searches. -/
def edges : Tree → Nat → Nat → Nat → Nat
  | .nil, _, _, _ => 0
  | .node l r, lo, old, new =>
      if old < lo + leaves l ∧ new < lo + leaves l then edges l lo old new
      else if lo + leaves l ≤ old ∧ lo + leaves l ≤ new then edges r (lo + leaves l) old new
      else Distance.depth (.node l r) lo old + Distance.depth (.node l r) lo new

end RotationBST.Geometric.GreedyASS.Reference.Transitions
