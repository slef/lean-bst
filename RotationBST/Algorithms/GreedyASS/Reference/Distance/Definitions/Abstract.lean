module

public import RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Distance

/-- Edge depth of a leaf in a reference subtree whose first rank is `lo`. -/
def depth : Tree → Nat → Nat → Nat
  | .nil, _, _ => 0
  | .node l r, lo, x =>
      if x < lo + leaves l then depth l lo x + 1
      else depth r (lo + leaves l) x + 1

/-- Edge depth of the lowest common ancestor of two reference leaves. -/
def lcaDepth : Tree → Nat → Nat → Nat → Nat
  | .nil, _, _, _ => 0
  | .node l r, lo, a, b =>
      if a < lo + leaves l ∧ b < lo + leaves l then lcaDepth l lo a b + 1
      else if lo + leaves l ≤ a ∧ lo + leaves l ≤ b then
        lcaDepth r (lo + leaves l) a b + 1
      else 0

/-- The actual subtree occurrence rooted at the lowest common ancestor. -/
def lca : Tree → Nat → Nat → Nat → Component
  | .nil, lo, _, _ => ⟨lo, .nil⟩
  | .node l r, lo, a, b =>
      if a < lo + leaves l ∧ b < lo + leaves l then lca l lo a b
      else if lo + leaves l ≤ a ∧ lo + leaves l ≤ b then
        lca r (lo + leaves l) a b
      else ⟨lo, .node l r⟩

/-- Subtree occurrences retain their offset and edge depth. Equal shapes at
different positions are distinct occurrences. -/
inductive Occurs : Tree → Nat → Component → Nat → Prop
  | root (t : Tree) (lo : Nat) : Occurs t lo ⟨lo, t⟩ 0
  | left {l r : Tree} {lo : Nat} {c : Component} {k : Nat} :
      Occurs l lo c k → Occurs (.node l r) lo c (k + 1)
  | right {l r : Tree} {lo : Nat} {c : Component} {k : Nat} :
      Occurs r (lo + leaves l) c k → Occurs (.node l r) lo c (k + 1)

/-- Node-counted distance to the LCA of enclosing leaves. The geometric
interpretation requires `a ≤ x ≤ b` and valid ranks. -/
def toLCA (t : Tree) (lo x a b : Nat) : Nat := depth t lo x - lcaDepth t lo a b + 1

/-- Node-counted distance from a contained leaf to the component root. -/
def toRoot (c : Component) (x : Nat) : Nat := depth c.shape c.first x + 1

end RotationBST.Geometric.GreedyASS.Reference.Distance
