module

public import RotationBST.Models.Pointer.Model
public import RotationBST.Models.Online.Abstract

@[expose] public section

/-! Bottom-up splaying of an inorder rank, using an explicit search zipper.
The four double cases are the Sleator--Tarjan zig-zig and zig-zag steps.
Weights used in the analysis are not stored in the tree or used by the algorithm.
Source: Sleator and Tarjan, Self-Adjusting Binary Search Trees (1985), Section 2. -/
namespace RotationBST.Splay
open Pointer

/-- Splay the focused node through its ancestors, two at a time. -/
def splayAt (l r : Tree) : List Frame → Tree
  | [] => .node l r
  | [.left b] => .node l (.node r b)
  | [.right a] => .node (.node a l) r
  | .left b :: .left c :: cs => splayAt l (.node r (.node b c)) cs
  | .right a :: .right b :: cs => splayAt (.node (.node b a) l) r cs
  | .right a :: .left b :: cs => splayAt (.node a l) (.node r b) cs
  | .left b :: .right a :: cs => splayAt (.node a l) (.node r b) cs

/-- Ordinary rank search; the nearest ancestor is first in the context. -/
def locate : Tree → Nat → Config
  | .nil, _ => ⟨.nil, []⟩
  | .node l r, x =>
      if x < l.size then
        let c := locate l x
        ⟨c.focus, c.context ++ [.left r]⟩
      else if x = l.size then ⟨.node l r, []⟩
      else
        let c := locate r (x - l.size - 1)
        ⟨c.focus, c.context ++ [.right l]⟩

/-- The returned count is the exact number of rotations, one per search ancestor.
Out-of-range inputs are outside the algorithm's correctness contract. -/
def run (t : Tree) (x : Nat) : Tree × Nat :=
  let c := locate t x
  match c.focus with
  | .nil => (t, 0)
  | .node l r => (splayAt l r c.context, c.context.length)

end RotationBST.Splay
