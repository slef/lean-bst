module

public import RotationBST.Structures.FingerHand.Definitions.Abstract
public import RotationBST.Structures.Tendon.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand

/-- A whole reference tree represented by pseudofinger vertices, incoming
compressed tendons, and untouched knuckle subtrees. Every `node` is one
pseudofinger; its incoming path may be empty. -/
inductive Hand where
  | knuckle (tree : Tree)
  | node (path : List Pointer.Frame) (tendon : Tendon.State) (left right : Hand)

namespace Hand

def count : Hand → Nat
  | .knuckle _ => 0
  | .node _ _ l r => l.count + 1 + r.count

def reference : Hand → Tree
  | .knuckle t => t
  | .node cs _ l r => Pointer.plug cs (.node l.reference r.reference)

def tree : Hand → Tree
  | .knuckle t => t
  | .node _ d l r => d.tree (.node l.tree r.tree)

/-- The pseudofinger skeleton, using global ranks from the reference tree. -/
def labels : Hand → Nat → LabelledTree Nat
  | .knuckle _, _ => .nil
  | .node cs _ l r, lo =>
      let base := lo + Pointer.offset cs
      .node (l.labels base) (base + l.reference.size) (r.labels (base + l.reference.size + 1))

def Valid : Hand → Prop
  | .knuckle _ => True
  | .node cs d l r => d.Represents cs ∧ l.Valid ∧ r.Valid

def potential : Hand → Nat
  | .knuckle _ => 0
  | .node _ d l r => d.potential + l.potential + r.potential

/-- Extend an incoming reference path during canonical construction. The newly
formed tendon is balanced; incremental updates use the tendon operations. -/
def extend (f : Pointer.Frame) : Hand → Hand
  | .knuckle t => .knuckle (Pointer.plug [f] t)
  | .node cs _ l r => .node (cs ++ [f]) (Tendon.State.ofPath (cs ++ [f])) l r

/-- Extract precisely the marked/branching skeleton used by `compress`, keeping
its suppressed paths as concrete two-deque tendons and its knuckles intact. -/
def build (marks : Finset Nat) : Tree → Nat → Hand
  | .nil, _ => .knuckle .nil
  | .node l r, lo =>
      let left := build marks l lo
      let right := build marks r (lo + l.size + 1)
      if lo + l.size ∈ marks then .node [] (Tendon.State.ofPath []) left right
      else match left, right with
        | .knuckle _, .knuckle _ => .knuckle (.node l r)
        | .knuckle _, q => q.extend (.right l)
        | q, .knuckle _ => q.extend (.left r)
        | q, s => .node [] (Tendon.State.ofPath []) q s

/-- Pack the fingers of a multifinger state, including its permanent root anchor. -/
def forState {k : Nat} (s : Multifinger.State k) : Hand := build (stateMarks s) s.tree 0

/-- The maintained representation invariant. Tendons may retain arbitrary valid
deque states; the reference tree and pseudofinger skeleton must match the
multifinger state exactly. -/
def Represents {k : Nat} (h : Hand) (s : Multifinger.State k) : Prop :=
  h.Valid ∧ h.reference = s.tree ∧ h.labels 0 = FingerHand.ofState s

end Hand
end RotationBST.FingerHand
