def Tree.size : Tree → Nat
  | .nil => 0
  | .node l r => l.size + 1 + r.size
