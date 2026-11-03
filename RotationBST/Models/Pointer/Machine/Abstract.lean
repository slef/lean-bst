module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! A single-finger BST machine. The cursor always points to an actual node
when an instruction is taken. Each parent/child move or rotation costs one;
a search starts at the root and must visit the requested inorder rank. -/
namespace RotationBST.Pointer

/-- The other child of an ancestor, together with the side containing the cursor. -/
inductive Frame where
  | left (right : Tree)
  | right (left : Tree)
  deriving DecidableEq, Repr

/-- Reassemble the whole tree from a focused subtree and its ancestors. -/
def plug : List Frame → Tree → Tree
  | [], t => t
  | .left r :: cs, t => plug cs (.node t r)
  | .right l :: cs, t => plug cs (.node l t)

/-- Number of keys before the focused subtree in the whole inorder traversal. -/
def offset : List Frame → Nat
  | [] => 0
  | .left _ :: cs => offset cs
  | .right l :: cs => offset cs + l.size + 1

structure Config where
  focus : Tree
  context : List Frame
  deriving DecidableEq, Repr

def Config.tree (c : Config) : Tree := plug c.context c.focus

def Config.key? (c : Config) : Option Nat :=
  match c.focus with
  | .nil => none
  | .node l _ => some (offset c.context + l.size)

/-- Move to a neighboring node, or rotate the pointed node over its parent.
A rotation keeps the cursor on that same node. -/
inductive Step : Config → Config → Prop where
  | downLeft {a b r : Tree} {cs : List Frame} : Step ⟨.node (.node a b) r, cs⟩ ⟨.node a b, .left r :: cs⟩
  | downRight {l a b : Tree} {cs : List Frame} : Step ⟨.node l (.node a b), cs⟩ ⟨.node a b, .right l :: cs⟩
  | upLeft {a b r : Tree} {cs : List Frame} : Step ⟨.node a b, .left r :: cs⟩ ⟨.node (.node a b) r, cs⟩
  | upRight {a b l : Tree} {cs : List Frame} : Step ⟨.node a b, .right l :: cs⟩ ⟨.node l (.node a b), cs⟩
  | rotateLeftChild {a b r : Tree} {cs : List Frame} : Step ⟨.node a b, .left r :: cs⟩ ⟨.node a (.node b r), cs⟩
  | rotateRightChild {a b l : Tree} {cs : List Frame} : Step ⟨.node a b, .right l :: cs⟩ ⟨.node (.node l a) b, cs⟩

/-- Exactly `k` charged instructions. -/
inductive Trace : Config → Config → Nat → Prop where
  | refl {c : Config} : Trace c c 0
  | step {a b c : Config} {k : Nat} : Step a b → Trace b c k → Trace a c (k + 1)

/-- A search visits `x`, possibly continues working, and finishes with tree `t`.
The extra unit accounts for the request itself. The final cursor is unrestricted;
the next request starts again at the root. -/
def Serves (s t : Tree) (x cost : Nat) : Prop :=
  ∃ visited finish before after,
    Trace ⟨s, []⟩ visited before ∧ visited.key? = some x ∧
    Trace visited finish after ∧ finish.tree = t ∧ cost = 1 + before + after

/-- A sequence of conventional searches with total instruction-and-request cost. -/
inductive Execution : Tree → List Nat → Tree → Nat → Prop where
  | nil {t : Tree} : Execution t [] t 0
  | cons {s t : Tree} {x k : Nat} {xs : List Nat} {u : Tree} {m : Nat} : Serves s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)

end RotationBST.Pointer
