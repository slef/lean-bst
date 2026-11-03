module

public import RotationBST.Structures.SplitTree.Multiway.Abstract

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway

/-- Repair a minimal first child, for every parent arity. A merge inside a
3- or 4-node removes a separator but preserves the parent's height. -/
def repairFirst : Multiway → Multiway × Nat
  | .three (.two a b) (.two c d) e => (.two (.four a b c d) e, 1)
  | .three (.two a b) (.three c d e) f => (.three (.three a b c) (.two d e) f, 4)
  | .three (.two a b) (.four c d e f) g => (.three (.three a b c) (.three d e f) g, 5)
  | .four (.two a b) (.two c d) e f => (.three (.four a b c d) e f, 0)
  | .four (.two a b) (.three c d e) f g => (.four (.three a b c) (.two d e) f g, 2)
  | .four (.two a b) (.four c d e f) g h => (.four (.three a b c) (.three d e f) g h, 3)
  | t => t.prepareLeft

/-- Repair a minimal last child, using its preceding sibling. -/
def repairLast : Multiway → Multiway × Nat
  | .three a (.two b c) (.two d e) => (.two a (.four b c d e), 0)
  | .three a (.three b c d) (.two e f) => (.three a (.two b c) (.three d e f), 2)
  | .three a (.four b c d e) (.two f g) => (.three a (.three b c d) (.three e f g), 4)
  | .four a b (.two c d) (.two e f) => (.three a b (.four c d e f), 1)
  | .four a b (.three c d e) (.two f g) => (.four a b (.two c d) (.three e f g), 2)
  | .four a b (.four c d e f) (.two g h) => (.four a b (.three c d e) (.three f g h), 4)
  | t => t.prepareRight

end RotationBST.Geometric.Split.Multiway
