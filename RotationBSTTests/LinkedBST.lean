module

public import RotationBST.Models.RealWorld.Linked.Abstract
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBSTTests.LinkedBST
open RotationBST RealWorld.Linked

def label (addr key : Nat) : Label 8 1 :=
  (addr, fun f => BitVec.ofNat 8 (if f = 0 then key else 10 * key))

def leaf (addr key : Nat) : Tree 8 1 := .node .nil (label addr key) .nil

def tree : Tree 8 1 :=
  .node (.node (.node (leaf 3 1) (label 2 2) (leaf 4 3)) (label 1 4) (leaf 5 6))
    (label 0 8) (leaf 6 10)

def cursor : Cursor 8 1 :=
  ⟨.node (leaf 3 1) (label 2 2) (leaf 4 3),
    [.left (label 1 4) (leaf 5 6), .left (label 0 8) (leaf 6 10)]⟩

def initial : State 8 1 2 :=
  ⟨0, fun r => if r = 0 then some 2 else if r = 1 then some 0 else none, fun _ => 0,
   [node (some 1) (some 6) none (label 0 8),
    node (some 2) (some 5) (some 0) (label 1 4),
    node (some 3) (some 4) (some 1) (label 2 2),
    node none none (some 2) (label 3 1),
    node none none (some 2) (label 4 3),
    node none none (some 1) (label 5 6),
    node none none (some 0) (label 6 10)]⟩

example : Realizes initial cursor := by
  constructor
  · constructor
    · intro r a ha
      fin_cases r <;> simp [initial] at ha <;> subst a <;> decide
    · intro rec mem f a ha
      simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        fin_cases f <;> simp [node] at ha <;> subst a <;> decide
  · simp [initial, cursor, Represents, parent, leaf, root, label]
  · simp [initial, cursor, Context, Represents, parent, leaf, root, label]
  · decide
  · intro a
    simp [initial, cursor, LabelledCursor.Config.tree, LabelledCursor.plug,
      addresses, LabelledTree.inorder, leaf, label]
    omega
  · simp [cursor, LabelledCursor.Config.tree, LabelledCursor.plug, keys,
      LabelledTree.Ordered, LabelledTree.inorder, leaf, label]
  · rfl
  · rfl
  · simp [cursor]

def rotated := run (program .rotateLeftChild) 18 (start initial)

-- Non-root rotation with a nonempty transferred subtree.
example : rotated.ptr 0 = some 2 ∧ rotated.ptr 1 = some 0 := by decide
example : (rotated.heap[0]).ptr 0 = some 2 := by decide
example : (rotated.heap[1]).ptr 0 = some 4 ∧ (rotated.heap[1]).ptr 2 = some 2 := by decide
example : (rotated.heap[4]).ptr 2 = some 1 := by decide
example : (rotated.heap[2]).ptr 1 = some 1 ∧ (rotated.heap[2]).ptr 2 = some 0 := by decide
example : rotated.heap.map (fun r => r.data 1) = initial.heap.map (fun r => r.data 1) := by decide

-- All four navigation opcodes follow the intended physical link.
example : (run (program .downLeft) 1 (start initial)).ptr 0 = some 3 := by decide
example : (run (program .downRight) 1 (start initial)).ptr 0 = some 4 := by decide
example : (run (program .upLeft) 1 (start initial)).ptr 0 = some 1 := by decide
example : (run (program .upRight) 1 (start (run (program .downRight) 1 (start initial)))).ptr 0 = some 2 := by decide

-- Right-child promotion, reconnecting through the grandparent's right link.
def rightInitial : State 8 1 2 :=
  ⟨0, fun r => if r = 0 then some 3 else if r = 1 then some 0 else none, fun _ => 0,
    [node none (some 1) none (label 0 0),
     node (some 2) (some 3) (some 0) (label 1 2),
     node none none (some 1) (label 2 1),
     node (some 4) none (some 1) (label 3 4),
     node none none (some 3) (label 4 3)]⟩

def rightRotated := run (program .rotateRightChild) 18 (start rightInitial)
example : (rightRotated.heap[0]).ptr 1 = some 3 := by decide
example : (rightRotated.heap[1]).ptr 1 = some 4 := by decide
example : (rightRotated.heap[4]).ptr 2 = some 1 := by decide
example : (rightRotated.heap[3]).ptr 0 = some 1 ∧ (rightRotated.heap[3]).ptr 2 = some 0 := by decide
example : rightRotated.ptr 1 = some 0 := by decide

-- Rotating a child of the root repairs the root register and null parent.
def rootInitial (right : Bool) : State 8 1 2 :=
  ⟨0, fun r => if r = 0 then some 1 else if r = 1 then some 0 else none, fun _ => 0,
    [node (if right then none else some 1) (if right then some 1 else none) none (label 0 2),
     node none none (some 0) (label 1 (if right then 3 else 1))]⟩

example : (run (program .rotateLeftChild) 18 (rootInitial false)).ptr 1 = some 1 := by decide
example : (run (program .rotateRightChild) 18 (rootInitial true)).ptr 1 = some 1 := by decide
example : ((run (program .rotateLeftChild) 18 (rootInitial false)).heap[1]).ptr 2 = none := by decide
example : ((run (program .rotateRightChild) 18 (rootInitial true)).heap[1]).ptr 2 = none := by decide

#print axioms RotationBST.RealWorld.Linked.Results.primitive
end RotationBSTTests.LinkedBST
