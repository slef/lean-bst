module

public import RotationBST.Structures.BSTDeque.Boundary.Definitions.Abstract

@[expose] public section
namespace RotationBST.Tendon

open Pointer.Lazy

/-- Side subtrees before the bottom endpoint, in inorder. The reference path
uses the same innermost-first convention as the pointer-machine zipper. -/
def lowerFringe : List Pointer.Frame → List Tree
  | [] => []
  | .left _ :: cs => lowerFringe cs
  | .right l :: cs => lowerFringe cs ++ [l]

/-- Side subtrees after the bottom endpoint, in inorder. -/
def upperFringe : List Pointer.Frame → List Tree
  | [] => []
  | .left r :: cs => r :: upperFringe cs
  | .right _ :: cs => upperFringe cs

/-- The endpoint is grafted into the maximum slot of the lower deque and the
minimum slot of the upper deque. The stored values of these two slots are ignored. -/
structure State where
  lower : BSTDeque.Deque
  upper : BSTDeque.Deque

namespace State

def context (d : State) : List Pointer.Frame := d.upper.minContext ++ d.lower.maxContext

def tree (d : State) (bottom : Tree) : Tree := Pointer.plug d.context bottom

/-- The complete active tendon region, with the endpoint subtree left opaque. -/
def skeleton (d : State) (bottom : Tree) : Skeleton :=
  d.lower.skeleton.fillMax (d.upper.skeleton.fillMin (.hole bottom))

def potential (d : State) : Nat := d.lower.potential + d.upper.potential

/-- A path representation retains every side subtree on its proper side of the
endpoint. Interleaving is recorded by the reference path, not inferred from keys. -/
def Represents (d : State) (cs : List Pointer.Frame) : Prop :=
  d.lower.fringe.dropLast = lowerFringe cs ∧ d.upper.fringe.tail = upperFringe cs

/-- A balanced initial representation of any concrete reference path. -/
def ofPath (cs : List Pointer.Frame) : State :=
  ⟨BSTDeque.Deque.balance (lowerFringe cs ++ [.nil]),
    BSTDeque.Deque.balance (.nil :: upperFringe cs)⟩

/-- Absorb the former top endpoint into the appropriate deque. The supplied
frame contains its off-path subtree. -/
def addTop (d : State) : Pointer.Frame → State
  | .right g => ⟨d.lower.pushFront g, d.upper⟩
  | .left g => ⟨d.lower, d.upper.pushBack g⟩

/-- Absorb the bottom's former parent. Its off-path subtree replaces the open
slot before the node is appended to the appropriate monotone component. -/
def addBottom (d : State) : Pointer.Frame → State
  | .right g => ⟨(d.lower.withMax g).pushBack .nil, d.upper⟩
  | .left g => ⟨d.lower, (d.upper.withMin g).pushFront .nil⟩

end State
end RotationBST.Tendon
