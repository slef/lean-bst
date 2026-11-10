module

public import RotationBST.Bounds.Interleave.Definitions.Abstract

@[expose] public section

/-! Tango's reference-tree vocabulary: preference switches along the reference
search path, tree height, perfect trees, and preferred paths. Wilber's
interleave quantity and its region bookkeeping are defined in
`Bounds/Interleave/Definitions/Abstract` under the `Wilber` namespace. -/
namespace RotationBST.Tango

/-- Actual preference switches on the reference search path for one request. -/
def changes : Tree → List Nat → Nat → Nat
  | .nil, _, _ => 0
  | .node l r, past, x =>
      if x < l.size + 1 + r.size then
        Wilber.switch (Wilber.regions l.size (l.size + 1 + r.size) past) (x ≤ l.size) +
        if x < l.size then changes l (Wilber.leftRequests l.size past) x
        else if x = l.size then 0
        else changes r (Wilber.rightRequests l.size past) (x - l.size - 1)
      else 0

/-- Total changes made while processing a sequence online. -/
def changeCost (t : Tree) : List Nat → List Nat → Nat
  | _, [] => 0
  | past, x :: xs => changes t past x + changeCost t (past ++ [x]) xs

/-! Height (`Tree.height`, the number of nodes on a longest root-to-leaf path)
bounds the number of keys in any preferred path, independently of how that path
is represented as an auxiliary balanced search tree. -/
export Tree (height)

/-- A perfect reference tree, useful when the key count is `2^h - 1`. -/
def perfect : Nat → Tree
  | 0 => .nil
  | h + 1 => .node (perfect h) (perfect h)

/-- A preferred path is an ordinary downward path in the reference tree. -/
inductive DownwardPath : Tree → List Bool → Prop
  | stop (l r : Tree) : DownwardPath (.node l r) []
  | left {l r : Tree} {path : List Bool} :
      DownwardPath l path → DownwardPath (.node l r) (true :: path)
  | right {l r : Tree} {path : List Bool} :
      DownwardPath r path → DownwardPath (.node l r) (false :: path)

end RotationBST.Tango
