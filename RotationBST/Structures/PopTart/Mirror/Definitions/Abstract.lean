module

public import RotationBST.Structures.PopTart.Definitions.Abstract
public import RotationBST.Models.Pointer.Mirror.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

/-- Reflection reverses the active skeleton and the physical fringe payloads.
To retain a payload's original orientation on the right stack, store its
reflection before reflecting the entire stack. -/
def mirror : WeightedTree → WeightedTree
  | .leaf t w => .leaf t.mirror w
  | .node l r => .node r.mirror l.mirror

end RotationBST.PopTart.WeightedTree
