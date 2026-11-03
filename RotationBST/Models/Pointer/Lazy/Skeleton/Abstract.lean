module

public import RotationBST.Models.Pointer.Traces

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

/-- The canonical right vine with these fringe subtrees in inorder. -/
def vine : List Tree → Tree
  | [] => .nil
  | [t] => t
  | t :: u :: ts => .node t (vine (u :: ts))

end Skeleton
end RotationBST.Pointer.Lazy
