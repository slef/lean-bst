module

public import RotationBST.Splay.Algorithm.Abstract

@[expose] public section

namespace RotationBST.Splay.Scanning

/-- Analysis-only marking. A hole is an entirely unmarked subtree; a node is
marked red. The actual splay algorithm never stores these marks. -/
inductive Marked where
  | hole (tree : Tree)
  | node (left right : Marked)

namespace Marked

def tree : Marked → Tree
  | .hole t => t
  | .node l r => .node l.tree r.tree

/-- Number of red nodes on the right spine. -/
def rank : Marked → Nat
  | .hole _ => 0
  | .node _ r => r.rank + 1

def Valid : Marked → Prop
  | .hole _ => True
  | .node l r => l.Valid ∧ r.Valid ∧ l.rank ≤ r.rank + 1

def alpha (v : Nat) : Nat := if v = 0 then 5 else 3 - v

def credit (g h : Nat) : Nat := h * h + 2 * alpha (g - h)

/-- Twice the red-node potential, plus a budget for first exposing each node.
The right-spine (black) nodes are accounted for by a constant per request. -/
def potential : Marked → Nat
  | .hole t => 18 * t.size
  | .node l r => l.potential + r.potential + credit (r.rank + 1) l.rank

end Marked
end RotationBST.Splay.Scanning
