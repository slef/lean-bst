module

public import RotationBST.Arboral.Treap.Regions.Abstract

@[expose] public section
namespace RotationBST.Arboral

/-- Latest touch in the recorded history; bottom means not yet touched. -/
def lastTouch (P : Finset Point) (key : Nat) : WithBot Nat :=
  ((P.filter fun p => p.1 = key).image Prod.snd).max

/-- The current tree is a max-heap of latest touches. -/
def HistoryHeap (P : Finset Point) (t : Tree) : Prop :=
  Heap (fun key => OrderDual.toDual (lastTouch P key)) t 0

/-- One search in the rooted-subtree version of the BST model. The active
region contains the requested key, and the inorder fringe is unchanged. -/
structure RegionStep (s t : Tree) (request : Nat) where
  before : Region
  after : Region
  source : before.tree = s
  target : after.tree = t
  fringe : before.fringe = after.fringe
  visits : request ∈ Region.keys before 0

/-- A sequence of rooted-region operations, charging the number of touched
nodes on each row. -/
inductive RegionExecution : Tree → List Nat → Tree → Nat → Prop
  | nil {t : Tree} : RegionExecution t [] t 0
  | cons {s t u : Tree} {x cost : Nat} {xs : List Nat} (step : RegionStep s t x) :
      RegionExecution t xs u cost →
      RegionExecution s (x :: xs) u (step.before.size + cost)

end RotationBST.Arboral
