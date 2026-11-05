module

public import RotationBST.Algorithms.OptimalLazyFinger.Definitions.Abstract
public import RotationBST.Algorithms.OptimalLazyFinger.Work.Model.Abstract

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work

/-- One read at each level of a dense matrix. -/
def matrixGet (t : PrefixSum.Table) (a b : Nat) : Computation Nat :=
  charge 2 (PrefixSum.get t a b)

/-- Two indexed updates and one scalar increment. -/
def increment (t : PrefixSum.Table) (a b : Nat) : Computation PrefixSum.Table :=
  charge 3 (Preprocessing.increment t a b)

def fill : PrefixSum.Table → Nat → List Nat → Computation PrefixSum.Table
  | t, _, [] => charge 1 t
  | t, p, x :: xs => do
      let next ← increment t p x
      let result ← fill next x xs
      charge 1 result

def frequencies (n p : Nat) (xs : List Nat) : Computation PrefixSum.Table := do
  let zeros ← arrayOfFn n (fun _ => replicate n 0)
  fill zeros p xs

/-- The input row itself may be a counted lookup computation. -/
def row (f : Nat → Computation Nat) : Nat → Computation (Array Nat)
  | 0 => charge 1 #[0]
  | n + 1 => do
      let previous ← row f n
      let x ← f n
      charge 4 (previous.push (previous[n]?.getD 0 + x))

def build (f : Nat → Nat → Computation Nat) (width : Nat) : Nat → Computation PrefixSum.Table
  | 0 => do
      let zeros ← replicate (width + 1) 0
      charge 1 #[zeros]
  | height + 1 => do
      let previous ← build f width height
      let horizontal ← row (f height) width
      let next ← arrayOfFn (width + 1) (fun b =>
        charge 4 (PrefixSum.get previous height b.val + horizontal[b.val]?.getD 0))
      charge 2 (previous.push next)

def prepare (n p : Nat) (xs : List Nat) : Computation PrefixSum.Table := do
  let f ← frequencies n p xs
  build (matrixGet f) n n

/-- Four matrix reads and three arithmetic operations. -/
def rectangle (p : PrefixSum.Table) (a b c d : Nat) : Computation Nat :=
  charge 11 (PrefixSum.rectangle p a b c d)

/-- Four rectangle queries and three additions: 47 RAM operations. -/
def toll (p : PrefixSum.Table) (n lo hi : Nat) : Computation Nat := do
  let a ← rectangle p lo hi 0 lo
  let b ← rectangle p lo hi hi n
  let c ← rectangle p 0 lo lo hi
  let d ← rectangle p hi n lo hi
  charge 3 (a + b + c + d)

def minimum (initial : Entry) : List Entry → Computation Entry
  | [] => charge 1 initial
  | x :: xs => do
      let tail ← minimum initial xs
      charge 2 (choose x tail)

/-- Five index arithmetic operations, two two-level table reads, two cost
additions, and a shape node allocation, in addition to the toll computation. -/
def candidate (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (n lo k : Nat) : Computation Entry := do
  let cost ← w lo (lo + n + 1)
  let l := lookup previous k lo
  let r := lookup previous (n - k) (lo + k + 1)
  charge 12 (.node l.1 r.1, cost + l.2 + r.2)

/-- One cached DP cell, including the extra initial candidate used by `minimum`. -/
def cell (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (N n lo : Nat) : Computation Entry := do
  let valid ← charge 3 (decide (lo + n + 1 ≤ N))
  if valid then
    let first ← candidate w previous n lo 0
    let indices ← charge (n + 2) (List.finRange (n + 1))
    let choices ← mapList (fun k => candidate w previous n lo k.val) indices
    minimum first choices
  else pure (.nil, 0)

def tabulate (w : Nat → Nat → Computation Nat) (N : Nat) : Nat → Computation (Array (Array Entry))
  | 0 => do
      let zeros ← replicate (N + 1) (.nil, 0)
      charge 1 #[zeros]
  | n + 1 => do
      let previous ← tabulate w N n
      let next ← arrayOfFn (N + 1) (fun lo => cell w previous N n lo.val)
      charge 2 (previous.push next)

def optimize (w : Nat → Nat → Computation Nat) (n : Nat) : Computation Entry := do
  let table ← tabulate w n n
  charge 2 (lookup table n 0)

/-- Counted executable optimizer, including preprocessing and initialization. -/
def treeFrom (n p : Nat) (xs : List Nat) : Computation Tree := do
  let prepared ← prepare (n + 1) p xs
  let result ← optimize (toll prepared (n + 1)) n
  pure result.1

def tree (n : Nat) (xs : List Nat) : Computation Tree := treeFrom n n xs

end RotationBST.OptimalLazyFinger.Work
