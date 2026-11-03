module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

/-- Current split choices only; a stopped interval is retained for later use. -/
inductive Plan where
  | stop
  | branch (rank : Nat) (left right : Plan)
  deriving DecidableEq, Repr

/-- Exposed separator keys with reusable shared intervals at the leaves. -/
inductive Partitioned where
  | leaf (interval : Option State)
  | branch (left right : Partitioned)
  deriving DecidableEq, Repr

def Partitioned.tree : Partitioned → Tree
  | .leaf interval => intervalTree interval
  | .branch l r => .node l.tree r.tree

def Partitioned.reserve : Partitioned → Nat
  | .leaf interval => intervalNodes interval
  | .branch l r => l.reserve + r.reserve

def Partitioned.Valid : Partitioned → Prop
  | .leaf interval => IntervalValid interval
  | .branch l r => l.Valid ∧ r.Valid

/-- Run a partial hierarchy, retaining rather than draining its stopped leaves. -/
def runPlan : Plan → Option State → Partitioned × Nat
  | .stop, input => (.leaf input, 0)
  | .branch _ _ _, none => (.leaf none, 0)
  | .branch rank l r, some state =>
      let cut := split state rank
      let left := runPlan l cut.left
      let right := runPlan r cut.right
      (.branch left.1 right.1, cut.cost + left.2 + right.2)

/-- Each requested split rank belongs to its current interval. -/
def Plan.Applicable : Plan → Option State → Prop
  | .stop, _ => True
  | .branch _ _ _, none => False
  | .branch rank l r, some state =>
      rank < state.size ∧ l.Applicable (split state rank).left ∧ r.Applicable (split state rank).right

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
