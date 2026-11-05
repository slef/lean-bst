module

public import RotationBST.Structures.BSTDeque.Definitions.Abstract

@[expose] public section
namespace RotationBST.BSTDeque.Deque

def minGap : Deque → Tree
  | .empty g => g
  | .node [] a _ _ => a
  | .node (g :: _) _ _ _ => g

def maxGap : Deque → Tree
  | .empty g => g
  | .node _ _ b [] => b
  | .node _ _ _ (g :: _) => g

/-- Change only the boundary hole, leaving every active node in place. -/
def withMin (q : Deque) (g : Tree) : Deque :=
  match q with
  | .empty _ => .empty g
  | .node [] _ b back => .node [] g b back
  | .node (_ :: gs) a b back => .node (g :: gs) a b back

def withMax (q : Deque) (g : Tree) : Deque :=
  match q with
  | .empty _ => .empty g
  | .node front a _ [] => .node front a g []
  | .node front a b (_ :: gs) => .node front a b (g :: gs)

/-- Context of the minimum-side fringe slot, at distance at most two. -/
def minContext : Deque → List Pointer.Frame
  | .empty _ => []
  | .node [] _ b back => [.left (backSpine back b).tree]
  | .node (_ :: gs) a b back =>
      [.left (frontSpine gs a).tree, .left (backSpine back b).tree]

/-- Context of the maximum-side fringe slot, at distance at most two. -/
def maxContext : Deque → List Pointer.Frame
  | .empty _ => []
  | .node front a _ [] => [.right (frontSpine front a).tree]
  | .node front a b (_ :: gs) =>
      [.right (backSpine gs b).tree, .right (frontSpine front a).tree]

end RotationBST.BSTDeque.Deque
