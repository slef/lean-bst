module

public import RotationBST.Algorithms.Splay.Updates.Algorithm.Abstract

@[expose] public section

namespace RotationBST.Splay.Updates

/-- Number of stored keys across the forest. -/
def forestSize (ts : List Tree) : Nat := (ts.map Tree.size).sum

/-- Standard successful operations, charged one unit plus their rotations.
`Step s t c n` records cost `c` and `n` participating keys before the operation.
Unrelated trees may be carried along; reordering the list of tree handles is free.
`join` requires that the left key set precede the right one; each input tree uses
local inorder ranks, and the joined tree uses their concatenation. -/
inductive Step : List Tree → List Tree → Nat → Nat → Prop where
  | access {x : Nat} {t : Tree} (valid : x < t.size) : Step [t] [(run t x).1] ((run t x).2 + 1) t.size
  | insert {k : Nat} {t : Tree} (valid : k ≤ t.size) : Step [t] [(insert t k).1] ((insert t k).2 + 1) t.size
  | delete {x : Nat} {t : Tree} (valid : x < t.size) : Step [t] [(delete t x).1] ((delete t x).2 + 1) t.size
  | split {k : Nat} {t : Tree} (valid : k ≤ t.size) : Step [t] [(split t k).left, (split t k).right] ((split t k).cost + 1) t.size
  | join {l r : Tree} : Step [l, r] [(join l r).1] ((join l r).2 + 1) (l.size + r.size)
  | frame {s t : List Tree} {k n : Nat} {a : Tree} : Step s t k n → Step (a :: s) (a :: t) k n
  | rearrange {s s' t' : List Tree} {k n : Nat} {t : List Tree} : s.Perm s' → Step s' t' k n → t'.Perm t → Step s t k n

/-- `m` operations, total cost `c`, with at most `N` stored keys at every boundary. -/
inductive Execution (N : Nat) : List Tree → Nat → List Tree → Nat → Prop where
  | nil {s : List Tree} (bound : forestSize s ≤ N) : Execution N s 0 s 0
  | cons {s t : List Tree} {k n m : Nat} {u : List Tree} {c : Nat} (bound : forestSize s ≤ N) : Step s t k n → Execution N t m u c →
      Execution N s (m + 1) u (k + c)

/-- An unbounded execution records the size of the tree(s) involved in each
operation. Unrelated trees do not contribute to that operation's logarithm. -/
inductive LocalExecution : List Tree → List Nat → List Tree → Nat → Prop where
  | nil {s : List Tree} : LocalExecution s [] s 0
  | cons {s t : List Tree} {k n : Nat} {ns : List Nat} {u : List Tree} {c : Nat} : Step s t k n → LocalExecution t ns u c → LocalExecution s (n :: ns) u (k + c)

end RotationBST.Splay.Updates
