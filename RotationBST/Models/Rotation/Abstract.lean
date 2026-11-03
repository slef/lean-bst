module

public import Std

@[expose] public section

/-! BST shapes: nodes have implicit zero-based inorder labels.
An access must put its requested label at the root. Cost counts rotations only,
including rotations inside subtrees; no pointer movement is charged. -/
namespace RotationBST

inductive Tree where
  | nil
  | node (left right : Tree)
  deriving DecidableEq, Repr

def Tree.size : Tree → Nat
  | .nil => 0
  | .node l r => l.size + 1 + r.size

/-- Number of edges on the search path to rank `x`. The empty case only makes
the function total; statements about searches require existing ranks. -/
def Tree.depth : Tree → Nat → Nat
  | .nil, _ => 0
  | .node l r, x =>
      if x < l.size then depth l x + 1
      else if x = l.size then 0
      else depth r (x - l.size - 1) + 1

/-- One rotation, at any depth. -/
inductive Rotate : Tree → Tree → Prop where
  | right {a b c : Tree} : Rotate (.node (.node a b) c) (.node a (.node b c))
  | left {a b c : Tree} : Rotate (.node a (.node b c)) (.node (.node a b) c)
  | inLeft {a b c : Tree} : Rotate a b → Rotate (.node a c) (.node b c)
  | inRight {a b c : Tree} : Rotate a b → Rotate (.node c a) (.node c b)

/-- Exactly `k` rotations. -/
inductive Rotations : Tree → Tree → Nat → Prop where
  | refl {t : Tree} : Rotations t t 0
  | step {s t u : Tree} {k : Nat} : Rotate s t → Rotations t u k → Rotations s u (k + 1)

/-- Access rank `x` from `s`, finish at `t`, using `k` rotations. -/
def Access (s t : Tree) (x k : Nat) : Prop :=
  Rotations s t k ∧ match t with
    | .nil => False
    | .node l _ => l.size = x

/-- An offline execution serving an entire request sequence. -/
inductive Execution : Tree → List Nat → Tree → Nat → Prop where
  | nil {t : Tree} : Execution t [] t 0
  | cons {s t : Tree} {x k : Nat} {xs : List Nat} {u : Tree} {m : Nat} : Access s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)

/-- A conventional node-labelled binary tree. Labels may be arbitrary keys. -/
inductive LabelledTree (α : Type) where
  | nil
  | node (left : LabelledTree α) (key : α) (right : LabelledTree α)
  deriving DecidableEq, Repr

/-- Forget the keys, keeping the entire shape. -/
def LabelledTree.erase {α : Type} : LabelledTree α → Tree
  | .nil => .nil
  | .node l _ r => .node l.erase r.erase

/-- Keys in symmetric (left, root, right) order. A BST on a specified sorted
key list is a labelled tree whose inorder traversal is that list. -/
def LabelledTree.inorder {α : Type} : LabelledTree α → List α
  | .nil => []
  | .node l x r => l.inorder ++ x :: r.inorder

/-- Label a shape by consecutive ranks, starting at `lo`. -/
def Tree.labelFrom : Tree → Nat → LabelledTree Nat
  | .nil, _ => .nil
  | .node l r, lo =>
      .node (l.labelFrom lo) (lo + l.size) (r.labelFrom (lo + l.size + 1))

/-- Ordinary rotations carry node labels with the nodes. -/
inductive LabelledTree.Rotate {α : Type} : LabelledTree α → LabelledTree α → Prop where
  | right {a : LabelledTree α} {x : α} {b : LabelledTree α} {y : α} {c : LabelledTree α} : Rotate (.node (.node a x b) y c) (.node a x (.node b y c))
  | left {a : LabelledTree α} {x : α} {b : LabelledTree α} {y : α} {c : LabelledTree α} : Rotate (.node a x (.node b y c)) (.node (.node a x b) y c)
  | inLeft {a b : LabelledTree α} {x : α} {c : LabelledTree α} : Rotate a b → Rotate (.node a x c) (.node b x c)
  | inRight {a b c : LabelledTree α} {x : α} : Rotate a b → Rotate (.node c x a) (.node c x b)

/-- Exactly `k` ordinary, label-preserving rotations. -/
inductive LabelledTree.Rotations {α : Type} : LabelledTree α → LabelledTree α → Nat → Prop where
  | refl {t : LabelledTree α} : Rotations t t 0
  | step {s t u : LabelledTree α} {k : Nat} : LabelledTree.Rotate s t → Rotations t u k → Rotations s u (k + 1)

/-- A labelled root access, with the same rotation-only cost convention. -/
def LabelledTree.Access {α : Type} (s t : LabelledTree α) (x : α) (k : Nat) : Prop :=
  LabelledTree.Rotations s t k ∧ match t with
    | .nil => False
    | .node _ y _ => y = x

/-- An ordinary labelled search sequence, with the same root-access convention. -/
inductive LabelledTree.Execution {α : Type} : LabelledTree α → List α → LabelledTree α → Nat → Prop where
  | nil {t : LabelledTree α} : Execution t [] t 0
  | cons {s t : LabelledTree α} {x : α} {k : Nat} {xs : List α} {u : LabelledTree α} {m : Nat} :
      LabelledTree.Access s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)

end RotationBST
