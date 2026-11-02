module

public import RotationBST.Splay.Algorithm.Abstract

@[expose] public section

/-! Standard splay updates on shapes. Each tree uses its own inorder ranks.
Splitting at gap `k` puts the first `k` keys on the left; joining concatenates
ordered key sets. Insert/delete renumber later ranks. Counts below are rotations;
the operation itself will add one unit in the forest execution model. -/
namespace RotationBST.Splay.Updates

structure SplitResult where
  left : Tree
  right : Tree
  cost : Nat
  deriving DecidableEq, Repr

/-- Split before rank `k` by splaying its predecessor. Valid gaps satisfy `k ≤ size`. -/
def split (t : Tree) (k : Nat) : SplitResult :=
  if k = 0 then ⟨.nil, t, 0⟩ else
    let (u, c) := run t (k - 1)
    match u with
    | .nil => ⟨.nil, .nil, c⟩
    | .node l r => ⟨.node l .nil, r, c⟩

/-- Join two ordered key sets by splaying the maximum of the left tree. -/
def join (l r : Tree) : Tree × Nat :=
  match l with
  | .nil => (r, 0)
  | .node _ _ =>
      let (u, c) := run l (l.size - 1)
      match u with
      | .nil => (r, c)
      | .node a _ => (.node a r, c)

/-- Insert a new key in gap `k`, making that key the root. -/
def insert (t : Tree) (k : Nat) : Tree × Nat :=
  let s := split t k
  (.node s.left s.right, s.cost)

/-- Delete existing rank `x`: splay it, remove the root, and join its children. -/
def delete (t : Tree) (x : Nat) : Tree × Nat :=
  let (u, c) := run t x
  match u with
  | .nil => (.nil, c)
  | .node l r =>
      let (v, d) := join l r
      (v, c + d)

end RotationBST.Splay.Updates
