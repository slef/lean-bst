module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! A dictionary model: accesses, insertions and deletions by rank on trees
that carry a datum in every node (a rank, a colour, a subtree size). Keys are
inorder ranks, as for shapes: inserting at gap `k` shifts every rank from `k`
on up by one, deleting rank `x` shifts every later rank down by one.

An operation is a sequence of primitive moves around at most one structural
change. The main cost charges the search path to the place of the change (to
`x` for an access) and every rotation; changes of node data are counted
separately. A search that changes nothing costs `1 + depth`. -/
namespace RotationBST

/-- The node of rank `x` has two nonempty children. -/
def Tree.TwoChildren : Tree → Nat → Prop
  | .nil, _ => False
  | .node l r, x =>
      if x < l.size then l.TwoChildren x
      else if x = l.size then l ≠ .nil ∧ r ≠ .nil
      else r.TwoChildren (x - l.size - 1)

/-- A shape with no node data. -/
def Tree.unit : Tree → LabelledTree Unit
  | .nil => .nil
  | .node l r => .node l.unit () r.unit

end RotationBST

namespace RotationBST.Dictionary

/-- A dictionary operation by rank. -/
inductive Op where
  | access (x : Nat)
  | insert (k : Nat)
  | delete (x : Nat)
  deriving DecidableEq, Repr

/-- An operation is valid on `n` keys when its rank exists (its gap, for an insertion). -/
def Op.Valid : Op → Nat → Prop
  | .access x, n => x < n
  | .insert k, n => k ≤ n
  | .delete x, n => x < n

/-- The number of keys after the operation. -/
def Op.resize : Op → Nat → Nat
  | .access _, n => n
  | .insert _, n => n + 1
  | .delete _, n => n - 1

/-- Every operation of a sequence is valid on the key count it meets. -/
def Op.ValidSeq : Nat → List Op → Prop
  | _, [] => True
  | n, op :: ops => op.Valid n ∧ Op.ValidSeq (op.resize n) ops

/-- Change the datum of one node. -/
inductive Edit {α : Type} : LabelledTree α → LabelledTree α → Prop where
  | here {l r : LabelledTree α} {d d' : α} : Edit (.node l d r) (.node l d' r)
  | inLeft {a b c : LabelledTree α} {d : α} : Edit a b → Edit (.node a d c) (.node b d c)
  | inRight {a b c : LabelledTree α} {d : α} : Edit a b → Edit (.node c d a) (.node c d b)

/-- `a` rotations and `e` data edits, in any order. Rotations carry data. -/
inductive Moves {α : Type} : LabelledTree α → LabelledTree α → Nat → Nat → Prop where
  | refl {t : LabelledTree α} : Moves t t 0 0
  | rotate {s t u : LabelledTree α} {a e : Nat} :
      LabelledTree.Rotate s t → Moves t u a e → Moves s u (a + 1) e
  | edit {s t u : LabelledTree α} {a e : Nat} : Edit s t → Moves t u a e → Moves s u a (e + 1)

/-- `Splice t x u`: the node of rank `x` in `t` has at most one child, and `u`
is `t` with that node removed, its child taking its place. Read backwards, it
inserts a node at rank `x` above a subtree or a leaf. -/
inductive Splice {α : Type} : LabelledTree α → Nat → LabelledTree α → Prop where
  | noLeft {d : α} {r : LabelledTree α} : Splice (.node .nil d r) 0 r
  | noRight {l : LabelledTree α} {d : α} : Splice (.node l d .nil) l.erase.size l
  | inLeft {l l' r : LabelledTree α} {d : α} {x : Nat} :
      Splice l x l' → Splice (.node l d r) x (.node l' d r)
  | inRight {l r r' : LabelledTree α} {d : α} {x : Nat} :
      Splice r x r' → Splice (.node l d r) (l.erase.size + 1 + x) (.node l d r')

/-- One operation from `s` to `t`, with main cost `c` and `e` data edits.

* An access to `x` pays `1 + depth x` in `s` and its moves.
* An insertion at gap `k` may move, then adds a node at rank `k` (a leaf, or
  above a subtree), then moves again. It pays `1 + depth k` of the new node
  and its rotations.
* A deletion of `x` may move, then splices out the node of rank `x`, or, when
  that node has two children, its predecessor or successor (whose datum is
  lost while the node at `x` keeps its own), then moves again. It pays
  `1 + depth` of the spliced node and its rotations. -/
inductive Step {α : Type} : LabelledTree α → Op → LabelledTree α → Nat → Nat → Prop where
  | access {s t : LabelledTree α} {x a e : Nat} (valid : x < s.erase.size) :
      Moves s t a e → Step s (.access x) t (s.erase.depth x + 1 + a) e
  | insert {s u v t : LabelledTree α} {k a₁ e₁ a₂ e₂ : Nat} (valid : k ≤ s.erase.size) :
      Moves s u a₁ e₁ → Splice v k u → Moves v t a₂ e₂ →
        Step s (.insert k) t (v.erase.depth k + 1 + a₁ + a₂) (e₁ + e₂)
  | delete {s u v t : LabelledTree α} {x y a₁ e₁ a₂ e₂ : Nat} (valid : x < s.erase.size)
      (target : y = x ∨ (u.erase.TwoChildren x ∧ (y + 1 = x ∨ y = x + 1))) :
      Moves s u a₁ e₁ → Splice u y v → Moves v t a₂ e₂ →
        Step s (.delete x) t (u.erase.depth y + 1 + a₁ + a₂) (e₁ + e₂)

/-- A sequence of operations, with total main cost `c` and `e` data edits. -/
inductive Execution {α : Type} : LabelledTree α → List Op → LabelledTree α → Nat → Nat → Prop where
  | nil {t : LabelledTree α} : Execution t [] t 0 0
  | cons {s t u : LabelledTree α} {op : Op} {ops : List Op} {c e c' e' : Nat} :
      Step s op t c e → Execution t ops u c' e' → Execution s (op :: ops) u (c + c') (e + e')

/-- An online dictionary algorithm. It sees the past operations, the current
tree and the current operation, and returns the new tree with its main cost
and data edits, certified by a `Step`. -/
structure Algorithm (α : Type) where
  step : List Op → LabelledTree α → Op → LabelledTree α × Nat × Nat
  correct : ∀ past t op, op.Valid t.erase.size →
    Step t op (step past t op).1 (step past t op).2.1 (step past t op).2.2

/-- Run from a tree, returning the final tree, main cost and data edits. -/
def Algorithm.runFrom {α : Type} (A : Algorithm α) (past : List Op) (t : LabelledTree α) :
    List Op → LabelledTree α × Nat × Nat
  | [] => (t, 0, 0)
  | op :: ops =>
      let r := A.step past t op
      let q := A.runFrom (past ++ [op]) r.1 ops
      (q.1, r.2.1 + q.2.1, r.2.2 + q.2.2)

end RotationBST.Dictionary
