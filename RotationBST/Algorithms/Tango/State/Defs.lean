module

public import RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Paths.Abstract

@[expose] public section
namespace RotationBST.Tango

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
def region : MarkedTree → Arboral.Region
  | .nil => .hole .nil
  | .node l r cl cr => .node
      (if cl then .hole l.tree else l.region)
      (if cr then .hole r.tree else r.region)

/-- A nonempty root component, with its global inorder offset. -/
def rootComponent (s : MarkedTree) (lo : Nat) : List (Nat × Arboral.Region) :=
  match s with
  | .nil => []
  | .node _ _ _ _ => [(lo, s.region)]

/-- Entire marked subtrees attached to the root component, in inorder. -/
def fringe : MarkedTree → List MarkedTree
  | .nil => [.nil]
  | .node l r cl cr => (if cl then [l] else l.fringe) ++ (if cr then [r] else r.fringe)

/-- The same marked fringe with absolute inorder offsets. -/
def fringeAt : MarkedTree → Nat → List (Nat × MarkedTree)
  | .nil, lo => [(lo, .nil)]
  | .node l r cl cr, lo =>
      (if cl then [(lo, l)] else l.fringeAt lo) ++
      (if cr then [(lo + l.tree.size + 1, r)] else r.fringeAt (lo + l.tree.size + 1))

/-- All components strictly below the root component. -/
def detached : MarkedTree → Nat → List (Nat × Arboral.Region)
  | .nil, _ => []
  | .node l r cl cr, lo =>
      (if cl then l.rootComponent lo else []) ++ l.detached lo ++
      (if cr then r.rootComponent (lo + l.tree.size + 1) else []) ++
      r.detached (lo + l.tree.size + 1)

def components (s : MarkedTree) (lo : Nat) : List (Nat × Arboral.Region) :=
  s.rootComponent lo ++ s.detached lo

/-- Total potential, summed over actual auxiliary components of the BST. -/
noncomputable def potential (s : MarkedTree) : ℝ :=
  ((s.components 0).map fun p => Arboral.Region.auxiliaryPotential p.2).sum

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
end RotationBST.Tango
