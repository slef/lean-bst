module

public import RotationBST.Algorithms.Simulation.Supernode.Defs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- One equal-priority layer with recursively heap-ordered gaps. The priority
bound covers its whole interval, including every key inside the gaps. -/
def Layer (P : Finset Point) (level : WithBot Nat) (region : Region) (lo : Nat) : Prop :=
  (∀ x < region.tree.size, lastTouch P (lo + x) ≤ level) ∧
  (∀ key ∈ Region.keys region lo, lastTouch P key = level) ∧
  ∀ hole ∈ Region.holes region lo,
    Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1

end RotationBST.Arboral.Online.Supernode
