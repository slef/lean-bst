module

public import RotationBST.Algorithms.Simulation.Supernode.Simulation.Defs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Persistent online simulation state, including the actual root-access tree
and the charged rotations needed to restore its canonical nested state. -/
structure Machine (n : Nat) where
  time : Nat
  points : Finset Point
  stored : Nested
  actual : Tree
  debt : Nat
  history : History n time points
  satisfied : ASS points
  represented : Represents points 0 stored
  size : stored.tree.size = n
  restore : Rotations actual stored.tree debt

/-- One certified online step. The geometric history and canonical stored
state advance using this request only. -/
def Machine.Step {n : Nat} (A : OnlineAlgorithm n) (before : Machine n)
    (request : Nat) (result : Machine n × Nat) : Prop :=
  result.1.time = before.time + 1 ∧
  result.1.points = before.points ∪ row before.time (A.step before.time request before.points) ∧
  result.1.stored = nextState before.stored (A.step before.time request before.points) ∧
  Access before.actual result.1.actual request result.2 ∧
  result.2 + result.1.debt + result.1.stored.credit ≤
    before.debt + before.stored.credit + 6018 * (A.step before.time request before.points).card

end RotationBST.Arboral.Online.Supernode
