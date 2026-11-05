module

public import RotationBST.Models.Pointer.Lazy.Skeleton.Abstract
public import Mathlib.Data.Nat.Dist

@[expose] public section

namespace RotationBST.BSTDeque

open Pointer.Lazy

/-- A right spine whose left subtrees are untouched fringe trees. -/
def frontSpine : List Tree → Tree → Skeleton
  | [], gap => .hole gap
  | g :: gs, gap => .node (.hole g) (frontSpine gs gap)

/-- A left spine, stored from maximum to minimum. -/
def backSpine : List Tree → Tree → Skeleton
  | [], gap => .hole gap
  | g :: gs, gap => .node (backSpine gs gap) (.hole g)

/-- A pivot separates two stacks of active BST nodes. The holes contain arbitrary
subtrees; their nodes are neither traversed nor charged by deque operations. -/
inductive Deque where
  | empty (gap : Tree)
  | node (front : List Tree) (leftGap rightGap : Tree) (back : List Tree)

namespace Deque

def skeleton : Deque → Skeleton
  | .empty gap => .hole gap
  | .node front a b back => .node (frontSpine front a) (backSpine back b)

def tree (q : Deque) : Tree := q.skeleton.tree

def size : Deque → Nat
  | .empty _ => 0
  | .node front _ _ back => front.length + 1 + back.length

/-- The complete inorder sequence of untouched fringe subtrees. -/
def fringe : Deque → List Tree
  | .empty gap => [gap]
  | .node front a b back => front ++ [a, b] ++ back.reverse

/-- Imbalance pays for occasional rebuilding when a stack becomes empty. -/
def potential : Deque → Nat
  | .empty _ => 0
  | .node front _ _ back => 32 * Nat.dist front.length back.length

/-- Build a balanced pair of stacks from an inorder fringe sequence. The empty
input is totalized; operations only rebuild nonempty sequences. -/
def balance (xs : List Tree) : Deque :=
  let k := (xs.length - 2) / 2
  match xs.drop k with
  | a :: b :: rest => .node (xs.take k) a b rest.reverse
  | [a] => .empty a
  | [] => .empty .nil

/-- The new minimum is initially supplied as the parent of the deque, with `g`
as its left subtree. -/
def pushFront (g : Tree) : Deque → Deque
  | .empty a => .node [] g a []
  | .node front a b back => .node (g :: front) a b back

/-- The new maximum is initially supplied as the parent of the deque. -/
def pushBack (g : Tree) : Deque → Deque
  | .empty a => .node [] a g []
  | .node front a b back => .node front a b (g :: back)

/-- Expose the minimum as a parent of the remaining deque, returning its left
fringe subtree. No tree node is deleted by the realizing pointer trace. -/
def popFront : Deque → Option (Tree × Deque)
  | .empty _ => none
  | .node (g :: gs) a b back => some (g, .node gs a b back)
  | .node [] a b back => some (a, balance (b :: back.reverse))

/-- Expose the maximum as a parent, returning its right fringe subtree. -/
def popBack : Deque → Option (Tree × Deque)
  | .empty _ => none
  | .node front a b (g :: gs) => some (g, .node front a b gs)
  | .node front a b [] => some (b, balance (front ++ [a]))

end Deque

/-- A legal deque operation. Pushes receive a node from the enclosing structure;
pops return one to it. The indices record the resulting deque state. -/
inductive Operation : Deque → Deque → Type where
  | pushFront (g : Tree) (q : Deque) : Operation q (q.pushFront g)
  | pushBack (g : Tree) (q : Deque) : Operation q (q.pushBack g)
  | popFront (q r : Deque) (g : Tree) (h : q.popFront = some (g, r)) : Operation q r
  | popBack (q r : Deque) (g : Tree) (h : q.popBack = some (g, r)) : Operation q r

namespace Operation

/-- Tree supplied by the caller at the operation boundary. -/
def input {q r : Deque} : Operation q r → Tree
  | .pushFront g q => .node g q.tree
  | .pushBack g q => .node q.tree g
  | .popFront q _ _ _ => q.tree
  | .popBack q _ _ _ => q.tree

/-- Tree returned at the boundary. A popped node remains as its root. -/
def output {q r : Deque} : Operation q r → Tree
  | .pushFront g q => (q.pushFront g).tree
  | .pushBack g q => (q.pushBack g).tree
  | .popFront _ r g _ => .node g r.tree
  | .popBack _ r g _ => .node r.tree g

def Realizes {q r : Deque} (op : Operation q r) (cost : Nat) : Prop :=
  Pointer.Trace ⟨op.input, []⟩ ⟨op.output, []⟩ cost

end Operation

/-- Any legal finite sequence, including arbitrary mixtures of both ends. -/
inductive Program : Deque → Deque → Nat → Type where
  | nil (q : Deque) : Program q q 0
  | cons {q r s : Deque} {n : Nat} (op : Operation q r) (rest : Program r s n) :
      Program q s (n + 1)

/-- A pointer realization of each operation at its stated input/output boundary.
The caller's transfer of nodes between boundaries is separate from this cost. -/
inductive Program.Realizes : {q r : Deque} → {n : Nat} → Program q r n → Nat → Prop where
  | nil (q : Deque) : Realizes (.nil q) 0
  | cons {q r s : Deque} {n k m : Nat} {op : Operation q r} {rest : Program r s n}
      (first : op.Realizes k) (tail : rest.Realizes m) :
      Realizes (.cons op rest) (k + m)

end RotationBST.BSTDeque
