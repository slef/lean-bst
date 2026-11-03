module

public import RotationBST.Structures.SplitTree.Multiway.Join.Left

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Join

/-- Count allocated multiway nodes, excluding a separator awaiting promotion. -/
def Promotion.nodes : Promotion → Nat
  | .stay t => t.nodes
  | .rise l r => l.nodes + r.nodes

theorem promotion_tree_nodes (up : Promotion) : up.tree.nodes ≤ up.nodes + 1 := by
  cases up <;> simp [Promotion.tree, Promotion.nodes, Multiway.nodes]

/-- Each crossed level can allocate at most one extra node during overflow. -/
theorem joinLeft_nodes (d : Nat) (l r : Multiway) :
    (joinLeft d l r).1.nodes ≤ l.nodes + r.nodes + d := by
  induction d generalizing r with
  | zero => simp [joinLeft, Promotion.nodes]
  | succ d ih =>
    cases r with
    | nil => simp [joinLeft, Promotion.nodes, Multiway.nodes]
    | two a b =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.nodes, Multiway.nodes] <;> omega
    | three a b c =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.nodes, Multiway.nodes] <;> omega
    | four a b c e =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.nodes, Multiway.nodes] <;> omega

/-- Each crossed level can allocate at most one extra node during overflow. -/
theorem joinRight_nodes (d : Nat) (l r : Multiway) :
    (joinRight d l r).1.nodes ≤ l.nodes + r.nodes + d := by
  induction d generalizing l with
  | zero => simp [joinRight, Promotion.nodes]
  | succ d ih =>
    cases l with
    | nil => simp [joinRight, Promotion.nodes, Multiway.nodes]
    | two a b =>
      have bound := ih b
      cases result : joinRight d b r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinRight, result, Promotion.nodes, Multiway.nodes] <;> omega
    | three a b c =>
      have bound := ih c
      cases result : joinRight d c r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinRight, result, Promotion.nodes, Multiway.nodes] <;> omega
    | four a b c e =>
      have bound := ih e
      cases result : joinRight d e r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.nodes] at bound <;>
          simp only [joinRight, result, Promotion.nodes, Multiway.nodes] <;> omega

end RotationBST.Arboral.Split.Multiway.Join
