module

public import RotationBST.Classical.WeightBalanced.Definitions.Abstract
public import RotationBST.Models.Dictionary.Definitions.Abstract
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-! Scapegoat trees (Galperin and Rivest; Andersson's general balanced trees):
plain insertions and deletions, with partial rebuilding. The parameter `α` is a
rational with `1/2 < α < 1`. The state is a shape and the count `N`, the
largest number of keys since the last rebuild of the whole tree. -/
namespace RotationBST.Classical.Scapegoat
open WeightBalanced

/-- Delete rank `x` without rebalancing: a node with at most one child is
spliced out; a node with two children loses its successor instead. -/
def bstDelete : Tree → Nat → Tree
  | .nil, _ => .nil
  | .node l r, x =>
      if x < l.size then .node (bstDelete l x) r
      else if x = l.size then
        match l, r with
        | .nil, _ => r
        | _, .nil => l
        | _, _ => .node l (bstDelete r 0)
      else .node l (bstDelete r (x - l.size - 1))

/-- The rank of the node that `bstDelete` removes: `x`, or its successor `x + 1`
when the node of rank `x` has two children. -/
def deleteTarget : Tree → Nat → Nat
  | .nil, x => x
  | .node l r, x =>
      if x < l.size then deleteTarget l x
      else if x = l.size then
        match l, r with
        | .nil, _ => x
        | _, .nil => x
        | _, _ => x + 1
      else l.size + 1 + deleteTarget r (x - l.size - 1)

/-- The subtree is too tall for its size: the node of rank `k` lies at depth
`d` with `α^d · size < 1`, that is `d > log_{1/α} size`. -/
def Violates (α : ℚ) (t : Tree) (k : Nat) : Prop := α ^ t.depth k * t.size < 1

instance (α : ℚ) (t : Tree) (k : Nat) : Decidable (Violates α t k) := by
  unfold Violates; infer_instance

/-- Rebuild the deepest subtree on the search path to `k` that violates the
height condition, if any; return the new tree and the rotations used. -/
def fix (α : ℚ) : Tree → Nat → Option (Tree × Nat)
  | .nil, _ => none
  | .node l r, k =>
      let below : Option (Tree × Nat) :=
        if k < l.size then (fix α l k).map fun p => (.node p.1 r, p.2)
        else if k = l.size then none
        else (fix α r (k - l.size - 1)).map fun p => (.node l p.1, p.2)
      match below with
      | some p => some p
      | none => if Violates α (.node l r) k then some (rebuild (.node l r)) else none

/-- A scapegoat tree: the shape and the count `N`. -/
abbrev State := Tree × Nat

/-- One operation: the new state and the main cost of the dictionary model
(`1 + depth` of the place of the change, plus rotations). An insertion
rebuilds the deepest violating subtree when the new leaf is deeper than
`log_{1/α} N`; a deletion rebuilds the whole tree when fewer than `α N` keys
remain. -/
def step (α : ℚ) (s : State) : Dictionary.Op → State × Nat
  | .access x => (s, s.1.depth x + 1)
  | .insert k =>
      let t₁ := Tree.insertAt s.1 k
      let N := max s.2 (s.1.size + 1)
      let d := t₁.depth k
      if α ^ d * N < 1 then
        match fix α t₁ k with
        | some p => ((p.1, N), d + 1 + p.2)
        | none => ((t₁, N), d + 1)
      else ((t₁, N), d + 1)
  | .delete x =>
      let t₁ := bstDelete s.1 x
      let c := s.1.depth (deleteTarget s.1 x) + 1
      if (t₁.size : ℚ) < α * s.2 then (((rebuild t₁).1, t₁.size), c + (rebuild t₁).2)
      else ((t₁, s.2), c)

/-- Run a sequence of operations, returning the final state and total cost. -/
def run (α : ℚ) (s : State) : List Dictionary.Op → State × Nat
  | [] => (s, 0)
  | op :: ops =>
      let r := step α s op
      let q := run α r.1 ops
      (q.1, r.2 + q.2)

/-- The key counts before each operation, starting from `n`. -/
def sizesFrom : Nat → List Dictionary.Op → List Nat
  | _, [] => []
  | n, op :: ops => n :: sizesFrom (op.resize n) ops

/-- The amortized cost of one operation on `n` keys:
`(2/(2α - 1) + 1)(log_{1/α} n + 2) + 1 + 2α/(1 - α)`. -/
noncomputable def bound (α : ℚ) (n : Nat) : ℝ :=
  (2 / (2 * (α : ℝ) - 1) + 1) * (Real.logb (1 / α) n + 2) + 1 + 2 * α / (1 - α)

end RotationBST.Classical.Scapegoat
