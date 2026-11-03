module

public import RotationBST.Models.Region.View.Abstract
public import RotationBST.Structures.Treap.Abstract

/-! Internal definitions of the region-model proofs: the history heap invariant
uses the treap order of `Structures/Treap`, a proof dependency only. -/

@[expose] public section
namespace RotationBST.Geometric

/-- Latest touch in the recorded history; bottom means not yet touched. -/
def lastTouch (P : Finset Point) (key : Nat) : WithBot Nat :=
  ((P.filter fun p => p.1 = key).image Prod.snd).max

/-- The current tree is a max-heap of latest touches. -/
def HistoryHeap (P : Finset Point) (t : Tree) : Prop :=
  Heap (fun key => OrderDual.toDual (lastTouch P key)) t 0

end RotationBST.Geometric
