module

public import RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Paths.Abstract

/-! Tango's state: a BST whose child edges carry marks. The marks split the
tree into auxiliary components, one per preferred path of the reference tree.
`Maintains` is the invariant that the marks realize the preferred paths after
the requests so far, with the nesting the reference tree prescribes. -/

@[expose] public section
namespace RotationBST.Tango
open Wilber

/-- A BST with marked child edges. A mark starts a new auxiliary component;
unmarked edges connect nodes within the same component. -/
inductive MarkedTree where
  | nil
  | node (left right : MarkedTree) (cutLeft cutRight : Bool)
  deriving DecidableEq, Repr

namespace MarkedTree

def tree : MarkedTree → Tree
  | .nil => .nil
  | .node l r _ _ => .node l.tree r.tree

/-- The auxiliary component at the root, with marked subtrees as holes. -/
def region : MarkedTree → Region
  | .nil => .hole .nil
  | .node l r cl cr => .node
      (if cl then .hole l.tree else l.region)
      (if cr then .hole r.tree else r.region)

/-- A nonempty root component, with its global inorder offset. -/
def rootComponent (s : MarkedTree) (lo : Nat) : List (Nat × Region) :=
  match s with
  | .nil => []
  | .node _ _ _ _ => [(lo, s.region)]

/-- All components strictly below the root component. -/
def detached : MarkedTree → Nat → List (Nat × Region)
  | .nil, _ => []
  | .node l r cl cr, lo =>
      (if cl then l.rootComponent lo else []) ++ l.detached lo ++
      (if cr then r.rootComponent (lo + l.tree.size + 1) else []) ++
      r.detached (lo + l.tree.size + 1)

def components (s : MarkedTree) (lo : Nat) : List (Nat × Region) :=
  s.rootComponent lo ++ s.detached lo

/-- Total potential, summed over actual auxiliary components of the BST. -/
noncomputable def potential (s : MarkedTree) : ℝ :=
  ((s.components 0).map fun p => Region.auxiliaryPotential p.2).sum

/-- Initially every reference node is its own component. -/
def initial : Tree → MarkedTree
  | .nil => .nil
  | .node l r => .node (initial l) (initial r) true true

/-- The marked components realize the preferred-path partition. Components are
compared as sets because auxiliary rotations change their depth order. The
root component must be the preferred path starting at the reference root. -/
def Represents (s : MarkedTree) (reference : Tree) (past : List Nat) : Prop :=
  s.tree.size = reference.size ∧
    ((s.components 0).map fun p => p.2.keys p.1).Perm
      ((preferredPaths reference past).map List.toFinset) ∧
    s.region.keys 0 = (decomposePaths reference 0 past).1.toFinset

end MarkedTree

/-- Ordered nesting of auxiliary components. A branch's children are its fringe
components, in key order; auxiliary BST shape is deliberately absent. -/
inductive ComponentNesting where
  | empty
  | branch (children : List ComponentNesting)
  deriving Repr

/-- An empty BST is one empty fringe slot. -/
def ComponentNesting.fringe : ComponentNesting → List ComponentNesting
  | .empty => [.empty]
  | .branch children => children

namespace MarkedTree

def nesting : MarkedTree → ComponentNesting
  | .nil => .empty
  | .node l r cl cr => .branch
      ((if cl then [nesting l] else (nesting l).fringe) ++
       (if cr then [nesting r] else (nesting r).fringe))

/-- The reference tree with exactly the preferred edges left unmarked. This
specifies the component nesting independently of auxiliary-tree rotations. -/
def canonical : Tree → Nat → List Nat → MarkedTree
  | .nil, _, _ => .nil
  | .node l r, lo, past =>
      let left := canonical l lo past
      let right := canonical r (lo + l.size + 1) past
      match (labels lo (lo + l.size) (lo + l.size + 1 + r.size) past).getLast? with
      | none => .node left right true true
      | some true => .node left right false true
      | some false => .node left right true false

/-- Full maintenance invariant: the preferred-path partition, its root path,
and the ordered nesting prescribed by the reference tree. -/
def Maintains (s : MarkedTree) (reference : Tree) (past : List Nat) : Prop :=
  Represents s reference past ∧ s.nesting = (canonical reference 0 past).nesting

end MarkedTree
end RotationBST.Tango
