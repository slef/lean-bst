module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section
namespace RotationBST.Tree

/-- Root-to-key search path in a shape whose inorder ranks start at `lo`.
Includes both root and requested key on valid inputs. Out-of-range requests
are totalized by following the corresponding unsuccessful search path. -/
def searchPath : Tree → Nat → Nat → List Nat
  | .nil, _, _ => []
  | .node l r, lo, x =>
    let root := lo + l.size
    if x < root then root :: searchPath l lo x
    else if x = root then [root]
    else root :: searchPath r (root + 1) x

end RotationBST.Tree
