module

public import RotationBST.Arboral.Treap.Regions.Abstract
public import RotationBST.Splay.Potential.Abstract
public import RotationBST.Splay.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Arboral.Region

/-- Shape of an auxiliary tree: each attached auxiliary subtree is a leaf. -/
def shape : Region → Tree
  | .hole _ => .nil
  | .node l r => .node (shape l) (shape r)

/-- Rank among the active keys, ignoring all attached fringe subtrees. -/
def index (s : Region) (lo key : Nat) : Nat := ((keys s lo).filter (· < key)).card

/-- Potential of the active auxiliary shape. Attached subtrees contribute no
mass, because they belong to other auxiliary components. -/
noncomputable def auxiliaryPotential (s : Region) : ℝ :=
  Splay.potential (fun _ => 1) (shape s) 0

/-- Fill a shape's external leaves with fringe subtrees in inorder. -/
def inflate : Tree → List Tree → Region
  | .nil, fringe => .hole (fringe.headD .nil)
  | .node l r, fringe => .node (inflate l fringe) (inflate r (fringe.drop (l.size + 1)))

/-- Splay an auxiliary rank while retaining the complete fringe. The count is
only the actual rotations; reconstruction is a pure presentation of their result. -/
def auxiliaryRun (s : Region) (k : Nat) : Region × Nat :=
  let result := Splay.run (shape s) k
  (inflate result.1 s.fringe, result.2)

end RotationBST.Arboral.Region
