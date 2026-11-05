module

public import RotationBST.Models.Labelled.Ordering.Definitions.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST

/-- Label a shape by an arbitrary inorder key list. Correctness requires matching
lengths; the default label only totalizes malformed preprocessing inputs. -/
def Tree.labelWith : Tree → List Nat → LabelledTree Nat
  | .nil, _ => .nil
  | .node l r, keys =>
      .node (l.labelWith (keys.take l.size)) ((keys[l.size]?).getD 0)
        (r.labelWith (keys.drop (l.size + 1)))

namespace LabelledTree

/-- Ordinary comparison search, returning membership and the number of visited
nodes. A failed search can visit nodes too; an empty tree visits none. -/
def lookup : LabelledTree Nat → Nat → Bool × Nat
  | .nil, _ => (false, 0)
  | .node l key r, x =>
      if x < key then let result := lookup l x; (result.1, result.2 + 1)
      else if x = key then (true, 1)
      else let result := lookup r x; (result.1, result.2 + 1)

/-- A legal static pointer search: compare at the current node, then follow
only the child selected by that comparison. Each visited node costs one unit.
The zero-cost empty case represents inspecting an already-null child pointer. -/
inductive Search : LabelledTree Nat → Nat → Bool → Nat → Prop where
  | empty (x : Nat) : Search .nil x false 0
  | found (l r : LabelledTree Nat) (x : Nat) : Search (.node l x r) x true 1
  | left {l r : LabelledTree Nat} {key x : Nat} {found : Bool} {cost : Nat} :
      x < key → Search l x found cost → Search (.node l key r) x found (cost + 1)
  | right {l r : LabelledTree Nat} {key x : Nat} {found : Bool} {cost : Nat} :
      key < x → Search r x found cost → Search (.node l key r) x found (cost + 1)

end LabelledTree
end RotationBST
