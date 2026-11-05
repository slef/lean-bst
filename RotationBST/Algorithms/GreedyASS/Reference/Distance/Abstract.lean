module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Reference.Distance.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Reference.Distance.Results

/-- The computed LCA is a common ancestor at the stated depth, and no common
ancestor occurrence has greater depth. Ranks use the reference leaf order. -/
theorem lowest_common_ancestor (t : Tree) (lo a b : Nat)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    Occurs t lo (lca t lo a b) (lcaDepth t lo a b) ∧
      (lca t lo a b).Contains a ∧ (lca t lo a b).Contains b ∧
      ∀ c k, Occurs t lo c k → c.Contains a → c.Contains b → k ≤ lcaDepth t lo a b :=
  ⟨lca_occurs t lo a b, (lca_contains t lo a b validA validB).1,
    (lca_contains t lo a b validA validB).2, fun _ _ occurs ha hb => lca_lowest occurs ha hb⟩

/-- The formula counts nodes on the upward path inside the actual LCA subtree. -/
theorem path (t : Tree) (lo a x b : Nat) (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    toLCA t lo x a b = toRoot (lca t lo a b) x := toLCA_eq t lo a x b ax xb validA validB

/-- Fact 3.1. The arithmetic inequalities also hold for totalized ranks;
their reference-path interpretation applies to valid leaves. -/
theorem ordered (t : Tree) (lo w x y z : Nat) (wx : w ≤ x) (xy : x ≤ y) (yz : y ≤ z) :
    toLCA t lo x w y ≤ toLCA t lo x w z ∧
      toLCA t lo y x z ≤ toLCA t lo y w z := four_leaves t lo w x y z wx xy yz

theorem interval (t : Tree) (lo x a b c d : Nat) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    toLCA t lo x b c ≤ toLCA t lo x a d := enclosing t lo x a b c d ab bc cd

theorem subtree {t : Tree} {lo k a x b : Nat} {c : Component}
    (occurs : Occurs t lo c k) (insideX : c.Contains x)
    (insideA : c.Contains a) (insideB : c.Contains b) :
    depth t lo x = k + depth c.shape c.first x ∧
      toLCA t lo x a b = toLCA c.shape c.first x a b :=
  ⟨occurs.depth_eq insideX, occurs.toLCA_eq insideX insideA insideB⟩

theorem forest (t : Tree) (lo searched : Nat) {c : Component}
    (member : c ∈ Reference.forest t lo searched) : ∃ k, Occurs t lo c k :=
  forest_occurs t lo searched member

/-- The distance comparison underlying Fact 3.2. Color assignment, missing
external neighbors, and the top-corner exception are separate obligations. -/
theorem component (t : Tree) (lo searched a x b : Nat) {c : Component}
    (member : c ∈ Reference.forest t lo searched) (inside : c.Contains x)
    (ax : a ≤ x) (xb : x ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    (toLCA t lo x a b ≤ toRoot c x ↔ c.Contains a ∧ c.Contains b) ∧
      (toRoot c x < toLCA t lo x a b ↔ ¬ c.Contains a ∨ ¬ c.Contains b) :=
  ⟨forest_compare t lo searched a x b member inside ax xb validA validB,
    forest_outside t lo searched a x b member inside ax xb validA validB⟩

/-- Each parent merge increases the node-counted distance by exactly one. -/
theorem merge (l r : Tree) (lo x : Nat) :
    (lo ≤ x ∧ x < lo + leaves l →
      toRoot ⟨lo, .node l r⟩ x = toRoot ⟨lo, l⟩ x + 1) ∧
    (lo + leaves l ≤ x ∧ x < lo + leaves l + leaves r →
      toRoot ⟨lo, .node l r⟩ x = toRoot ⟨lo + leaves l, r⟩ x + 1) :=
  ⟨merge_left l r lo x, merge_right l r lo x⟩

end RotationBST.Geometric.GreedyASS.Reference.Distance.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Reference.Distance.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Reference.Distance.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract]
