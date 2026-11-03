module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

namespace RotationBST

/-- An online rule sees only past requests, the current tree and current request.
For each existing rank, it returns a tree and a certified rotation count. -/
structure Algorithm where
  step : List Nat → Tree → Nat → Tree × Nat
  correct : ∀ past t x, x < t.size →
    Access t (step past t x).1 x (step past t x).2

def Algorithm.runFrom (a : Algorithm) (past : List Nat) (t : Tree) :
    List Nat → Tree × Nat
  | [] => (t, 0)
  | x :: xs =>
      let (u, k) := a.step past t x
      let (v, m) := a.runFrom (past ++ [x]) u xs
      (v, k + m)

def Algorithm.cost (a : Algorithm) (t : Tree) (xs : List Nat) : Nat :=
  (a.runFrom [] t xs).2

/-- Compare against every legal offline execution from the same initial tree. -/
def DynamicallyOptimal (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs u k, Execution t xs u k →
    a.cost t xs ≤ C * k + D * t.size

/-- Conventional cost: one unit per request, plus rotations. -/
def Algorithm.totalCost (a : Algorithm) (t : Tree) (xs : List Nat) : Nat :=
  xs.length + a.cost t xs

/-- Conventional competitiveness; constants are uniform in size and sequence. -/
def TotallyDynamicallyOptimal (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs u k, Execution t xs u k →
    a.totalCost t xs ≤ C * (xs.length + k) + D * t.size

end RotationBST
