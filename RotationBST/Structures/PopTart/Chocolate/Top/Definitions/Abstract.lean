module

public import RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Layer

/-- The first outer crumb. At level zero it is one opaque payload. -/
def top : Layer → WeightedTree
  | .last .zero icing => icing.decode
  | .next .zero child icing => .node child.decode icing.decode
  | .last (.one a) _ | .last (.two a _) _ | .last (.three a _ _) _ => a
  | .next (.one a) _ _ | .next (.two a _) _ _ | .next (.three a _ _) _ _ => a

/-- The unchanged suffix beyond the first separator, if that separator exists. -/
def topTail : Layer → Option WeightedTree
  | .last .zero _ | .next .zero _ _ => none
  | .last (.one _) icing => some icing.decode
  | .last (.two _ b) icing => some (.node b icing.decode)
  | .last (.three _ b c) icing => some (.node b (.node c icing.decode))
  | .next (.one _) child icing => some (.node child.decode icing.decode)
  | .next (.two _ b) child icing => some (.node b (.node child.decode icing.decode))
  | .next (.three _ b c) child icing => some (.node b (.node c (.node child.decode icing.decode)))

/-- Update the opaque first payload without touching the suffix metadata.
This is a representation operation, not a free physical change of subtree. -/
def replaceTop (new : WeightedTree) : Layer → Layer
  | .last .zero _ | .next .zero _ _ => .last .zero (.base new)
  | .last (.one _) icing => .last (.one new) icing
  | .last (.two _ b) icing => .last (.two new b) icing
  | .last (.three _ b c) icing => .last (.three new b c) icing
  | .next (.one _) child icing => .next (.one new) child icing
  | .next (.two _ b) child icing => .next (.two new b) child icing
  | .next (.three _ b c) child icing => .next (.three new b c) child icing

end RotationBST.PopTart.Chocolate.Layer
