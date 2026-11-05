module

public import RotationBST.Models.Rotation.Abstract
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace RotationBST.LinkedSearch

/-- A search node carries a comparison key and a stored successor-root pointer.
The two child pointers are supplied by `LabelledTree.node`. -/
structure Entry (ι : Type) where
  key : Nat
  next : ι
  deriving DecidableEq, Repr

/-- An immutable finite directory of local roots and one shared fallback root.
An index of type `ι` is a root-cell address, not a key used to search the directory.
Reading a stored successor pointer and following it costs one in `Request`.
The function denotes the contents of a root table in this pointer model;
its Lean evaluation or closure allocation is not a machine-cost semantics. -/
structure Store (ι : Type) where
  roots : ι → LabelledTree (Entry ι)
  fallback : LabelledTree (Entry ι)

/-- Storage in nodes, counting every local tree and the shared fallback once. -/
def Store.nodes {ι : Type} [Fintype ι] (s : Store ι) : Nat :=
  (∑ p, (s.roots p).erase.size) + s.fallback.erase.size

/-- Four words per node (key, successor, and two children), one word per local
root cell, and a fallback-root word. The running cursor needs constant space. -/
def Store.words {ι : Type} [Fintype ι] (s : Store ι) : Nat :=
  4 * s.nodes + Fintype.card ι + 1

/-- Install successor pointers during preprocessing. They are then explicit
fields of stored nodes, not computed from requested keys at query time. -/
def attach {ι : Type} (target : Nat → ι) : LabelledTree Nat → LabelledTree (Entry ι)
  | .nil => .nil
  | .node l key r => .node (attach target l) ⟨key, target key⟩ (attach target r)

/-- Compare at a node and follow the selected child. A hit returns the stored
successor pointer; a miss returns none. Cost counts visited nodes. -/
def lookup {ι : Type} : LabelledTree (Entry ι) → Nat → Option ι × Nat
  | .nil, _ => (none, 0)
  | .node l entry r, x =>
      if x < entry.key then let result := lookup l x; (result.1, result.2 + 1)
      else if x = entry.key then (some entry.next, 1)
      else let result := lookup r x; (result.1, result.2 + 1)

/-- Operational search semantics expose only comparisons and child traversals.
One node visit charges a constant unit for these primitive operations. -/
inductive Search {ι : Type} : LabelledTree (Entry ι) → Nat → Option ι → Nat → Prop where
  | empty (x : Nat) : Search .nil x none 0
  | found (l r : LabelledTree (Entry ι)) (entry : Entry ι) :
      Search (.node l entry r) entry.key (some entry.next) 1
  | left {l r : LabelledTree (Entry ι)} {entry : Entry ι} {x cost : Nat} {next : Option ι} :
      x < entry.key → Search l x next cost → Search (.node l entry r) x next (cost + 1)
  | right {l r : LabelledTree (Entry ι)} {entry : Entry ι} {x cost : Nat} {next : Option ι} :
      entry.key < x → Search r x next cost → Search (.node l entry r) x next (cost + 1)

/-- A hit follows the found node's successor pointer. A miss first follows the
shared fallback pointer, searches there, then follows its found successor. -/
inductive Request {ι : Type} (s : Store ι) (current : ι) (x : Nat) : ι → Nat → Prop where
  | hit {next : ι} {k : Nat} : Search (s.roots current) x (some next) k →
      Request s current x next (k + 1)
  | miss {next : ι} {k h : Nat} : Search (s.roots current) x none k →
      Search s.fallback x (some next) h → Request s current x next (k + h + 2)

/-- The executable query rule includes a charged fallback on a local miss. -/
def request {ι : Type} (s : Store ι) (current : ι) (x : Nat) : Option ι × Nat :=
  let first := lookup (s.roots current) x
  match first.1 with
  | some next => (some next, first.2 + 1)
  | none => let last := lookup s.fallback x; (last.1, first.2 + last.2 + 2)

inductive Execution {ι : Type} (s : Store ι) : ι → List Nat → ι → Nat → Prop where
  | nil {p : ι} : Execution s p [] p 0
  | cons {p q r : ι} {x k h : Nat} {xs : List Nat} :
      Request s p x q k → Execution s q xs r h → Execution s p (x :: xs) r (k + h)

end RotationBST.LinkedSearch
