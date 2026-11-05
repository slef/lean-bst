module

public import RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Conversion

/-- Replace each ordinary BST key by a leaf, retaining inorder ranks and
contracting missing children. The empty input is totalized to one leaf;
population and performance theorems require a nonempty input. -/
def convert : Tree → Tree
  | .nil => .nil
  | .node l r =>
    if l.size = 0 then
      if r.size = 0 then .nil else .node .nil (convert r)
    else
      if r.size = 0 then .node (convert l) .nil
      else .node (convert l) (.node .nil (convert r))

end RotationBST.Geometric.GreedyASS.Reference.Conversion
