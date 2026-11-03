module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs
public import RotationBST.Structures.SplitTree.Accounting.Abstract

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded

/-- Execute a complete hierarchy of splits. Each node chooses its separating
rank by the size of the requested left interval and recurses on the normalized
outputs. The hierarchy supplies split choices, not a precomputed rotation path. -/
def hierarchyCost : Tree → Option State → Nat
  | .nil, _ => 0
  | .node _ _, none => 0
  | .node l r, some state =>
      let result := split state l.size
      result.cost + hierarchyCost l result.left + hierarchyCost r result.right

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded
