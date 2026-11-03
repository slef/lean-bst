module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Defs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Store the exposed keys in a fresh shared supernode and retain the exact
ordered nested children. An empty exposed region retains its sole child. -/
def Assembly.rebuild (assembly : Assembly) : Nested :=
  match initialInterval assembly.shape.size with
  | none => (assembly.children[0]?).getD .empty
  | some state => .layer state assembly.children

end RotationBST.Arboral.Online.Supernode
