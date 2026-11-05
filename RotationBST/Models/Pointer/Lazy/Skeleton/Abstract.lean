module

public import RotationBST.Models.Pointer.Machine.Abstract

@[expose] public section

namespace RotationBST.Pointer.Lazy

/-- A connected region of a tree. A hole holds an entire untouched fringe subtree;
only `node` constructors count toward the size of the region. -/
inductive Skeleton where
  | hole (tree : Tree)
  | node (left right : Skeleton)

namespace Skeleton

def tree : Skeleton → Tree
  | .hole t => t
  | .node l r => .node l.tree r.tree

def size : Skeleton → Nat
  | .hole _ => 0
  | .node l r => l.size + 1 + r.size

def fringe : Skeleton → List Tree
  | .hole t => [t]
  | .node l r => l.fringe ++ r.fringe

/-- Substitute a connected region for the first or last inorder hole. -/
def fillMin : Skeleton → Skeleton → Skeleton
  | .hole _, t => t
  | .node l r, t => .node (l.fillMin t) r

def fillMax : Skeleton → Skeleton → Skeleton
  | .hole _, t => t
  | .node l r, t => .node l (r.fillMax t)

/-- A zipper path as an active skeleton, keeping each off-path subtree opaque. -/
def under : Skeleton → List Pointer.Frame → Skeleton
  | s, [] => s
  | s, .left r :: cs => (Skeleton.node s (.hole r)).under cs
  | s, .right l :: cs => (Skeleton.node (.hole l) s).under cs

/-- The canonical right vine with these fringe subtrees in inorder. -/
def vine : List Tree → Tree
  | [] => .nil
  | [t] => t
  | t :: u :: ts => .node t (vine (u :: ts))

end Skeleton
end RotationBST.Pointer.Lazy
