module

public import RotationBST.Tango.State.Rebuild.Abstract
public import RotationBST.Splay.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Splay an active rank within the root component, reconstructing its marked
fringe in the new shape. The result contains the whole BST and rotation count. -/
def splayRoot (s : MarkedTree) (rank : Nat) : MarkedTree × Nat :=
  let (shape, cost) := Splay.run (Arboral.Region.shape s.region) rank
  (rebuild shape s.fringe, cost)

end RotationBST.Tango.MarkedTree
