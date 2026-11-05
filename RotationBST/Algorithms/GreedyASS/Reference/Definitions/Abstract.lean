module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference

/-- The reference tree is leaf-oriented: `Tree.nil` is one labelled leaf,
and a node joins two nonempty leaf ranges. Ordinary BST node ranks are not
used for this reference tree. -/
def leaves : Tree → Nat
  | .nil => 1
  | .node l r => leaves l + leaves r

/-- A subtree occurrence, identified by its shape and first leaf rank. -/
structure Component where
  first : Nat
  shape : Tree
  deriving DecidableEq, Repr

def Component.last (c : Component) : Nat := c.first + leaves c.shape

def Component.Contains (c : Component) (key : Nat) : Prop :=
  c.first ≤ key ∧ key < c.last

instance (c : Component) (key : Nat) : Decidable (c.Contains key) :=
  inferInstanceAs (Decidable (c.first ≤ key ∧ key < c.last))

/-- Remove the proper ancestors of the searched leaf. The resulting forest
is listed in increasing leaf order and includes the searched singleton.
Invalid searches are totalized; search-side theorems require a valid rank. -/
def forest : Tree → Nat → Nat → List Component
  | .nil, lo, _ => [⟨lo, .nil⟩]
  | .node l r, lo, searched =>
      if searched < lo + leaves l then
        forest l lo searched ++ [⟨lo + leaves l, r⟩]
      else
        ⟨lo, l⟩ :: forest r (lo + leaves l) searched

end RotationBST.Geometric.GreedyASS.Reference
