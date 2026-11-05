module

public import RotationBST.Structures.FingerHand.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand

/-- Retain a marked root or a branch; contract an unmarked unary root. -/
def join (marks : Finset Nat) (l : LabelledTree Nat) (x : Nat) (r : LabelledTree Nat) : LabelledTree Nat :=
  if x ∈ marks then .node l x r
  else match l, r with
    | .nil, _ => r
    | _, .nil => l
    | _, _ => .node l x r

/-- Recompute a marked skeleton using its existing labels, without relabelling
the surviving vertices by consecutive ranks. -/
def prune (marks : Finset Nat) : LabelledTree Nat → LabelledTree Nat
  | .nil => .nil
  | .node l x r => join marks (prune marks l) x (prune marks r)

/-- Count occurrences of marks that disappear. On a distinctly labelled tree,
erasing one key contributes at most one to this quantity. -/
def lostMarks (before after : Finset Nat) : LabelledTree Nat → Nat
  | .nil => 0
  | .node l x r => lostMarks before after l +
      (if x ∈ before ∧ x ∉ after then 1 else 0) + lostMarks before after r

/-- Counting a nonempty skeleton with an extra root unit makes the loss of
branch vertices telescope when terminals are removed. -/
def skeletonMass (t : LabelledTree Nat) : Nat := t.erase.size + if t = .nil then 0 else 1

/-- A skeleton obtained by discarding subtrees and contracting unary paths.
Surviving vertices keep their labels and ancestor relationships. -/
inductive Contracts : LabelledTree Nat → LabelledTree Nat → Prop where
  | empty (t : LabelledTree Nat) : Contracts t .nil
  | node {l r a b : LabelledTree Nat} (x : Nat) :
      Contracts l a → Contracts r b → Contracts (.node l x r) (.node a x b)
  | left {l r a : LabelledTree Nat} (x : Nat) : Contracts l a → Contracts (.node l x r) a
  | right {l r b : LabelledTree Nat} (x : Nat) : Contracts r b → Contracts (.node l x r) b

/-- The root anchor and every finger except the one being moved. A coincident
inactive finger keeps its key in this set. -/
def stationaryMarks {k : Nat} (s : Multifinger.State k) (i : Fin k) : Finset Nat :=
  insert (rootRank s.tree) ((Finset.univ.erase i).image s.position)

/-- A reference rotation whose two participating keys are retained as marks.
The enclosing vertices need not be marked. -/
inductive MarkedRotation (marks : Finset Nat) : LabelledTree Nat → LabelledTree Nat → Prop where
  | right {a b c : LabelledTree Nat} {x y : Nat} : x ∈ marks → y ∈ marks →
      MarkedRotation marks (.node (.node a x b) y c) (.node a x (.node b y c))
  | left {a b c : LabelledTree Nat} {x y : Nat} : x ∈ marks → y ∈ marks →
      MarkedRotation marks (.node a x (.node b y c)) (.node (.node a x b) y c)
  | inLeft {a b c : LabelledTree Nat} {x : Nat} : MarkedRotation marks a b →
      MarkedRotation marks (.node a x c) (.node b x c)
  | inRight {a b c : LabelledTree Nat} {x : Nat} : MarkedRotation marks a b →
      MarkedRotation marks (.node c x a) (.node c x b)

end RotationBST.FingerHand
