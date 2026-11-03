module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded

/-- Empty intervals have no separating root. -/
def intervalTree : Option State → Tree
  | none => .nil
  | some state => state.tree

/-- Reserve carried by a reusable interval, including its separating root. -/
def intervalNodes : Option State → Nat
  | none => 0
  | some state => state.left.tree.nodes + state.right.tree.nodes + 1

def IntervalValid : Option State → Prop
  | none => True
  | some state => state.HeightValid

/-- Restore a reusable shared representation, charging every conversion and
rebalance rotation. An empty single-finger interval stays empty. -/
def normalize : Fragment → Option State × Nat
  | .minimum p =>
      if p.tree = .nil then (none, 0)
      else
        let result := fromRoot p.height p.tree
        (some result.1, conversionCost p.tree + result.2)
  | .maximum p =>
      if p.tree = .nil then (none, 0)
      else
        let result := fromRoot p.height p.tree
        (some result.1, maximumCost p.tree + result.2)
  | .shared state =>
      let result := rebalance state
      (some result.1, result.2)

/-- Complete shared-root split, including normalization of both outputs. -/
structure SplitResult where
  left : Option State
  right : Option State
  cost : Nat
  deriving DecidableEq, Repr

def SplitResult.tree (result : SplitResult) : Tree := .node (intervalTree result.left) (intervalTree result.right)

def split (state : State) (rank : Nat) : SplitResult :=
  let exposed := expose state rank
  let left := normalize exposed.left
  let right := normalize exposed.right
  ⟨left.1, right.1, exposed.cost + left.2 + right.2⟩

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded
