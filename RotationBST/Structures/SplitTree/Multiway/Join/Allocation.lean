module

public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Join

/-- The executable join allocates at most one node plus its rotation count. -/
theorem joinRight_allocation (d : Nat) (l r : Multiway) :
    (joinRight d l r).1.tree.nodes ≤ l.nodes + r.nodes + (joinRight d l r).2 + 1 := by
  induction d generalizing l with
  | zero => simp [joinRight, Promotion.tree, Multiway.nodes]
  | succ d ih =>
    cases l with
    | nil => simp [joinRight, Promotion.tree, Multiway.nodes]
    | two a b =>
      have bound := ih b
      cases result : joinRight d b r with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinRight, result, Promotion.tree, Multiway.nodes] <;> omega
    | three a b c =>
      have bound := ih c
      cases result : joinRight d c r with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinRight, result, Promotion.tree, Multiway.nodes] <;> omega
    | four a b c e =>
      have bound := ih e
      cases result : joinRight d e r with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinRight, result, Promotion.tree, Multiway.nodes] <;> omega

theorem joinLeft_allocation (d : Nat) (l r : Multiway) :
    (joinLeft d l r).1.tree.nodes ≤ l.nodes + r.nodes + (joinLeft d l r).2 + 1 := by
  induction d generalizing r with
  | zero => simp [joinLeft, Promotion.tree, Multiway.nodes]
  | succ d ih =>
    cases r with
    | nil => simp [joinLeft, Promotion.tree, Multiway.nodes]
    | two a b =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.tree, Multiway.nodes] <;> omega
    | three a b c =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.tree, Multiway.nodes] <;> omega
    | four a b c e =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result, Promotion.tree, Multiway.nodes] at bound <;>
          simp only [joinLeft, result, Promotion.tree, Multiway.nodes] <;> omega

theorem run_allocation (hl hr : Nat) (l r : Multiway) :
    (run hl hr l r).tree.nodes ≤ l.nodes + r.nodes + (run hl hr l r).cost + 1 := by
  unfold run
  split <;> simp only [finish_tree, finish_cost]
  · exact joinRight_allocation _ _ _
  · exact joinLeft_allocation _ _ _

theorem compact_allocation (hl hr : Nat) (l r : Multiway) :
    (compact hl hr l r).tree.nodes ≤ l.nodes + r.nodes + (compact hl hr l r).cost + 1 := by
  by_cases eq : hl = hr
  · cases l <;> cases r <;> simp only [compact, eq, ite_true] <;> try exact run_allocation _ _ _ _
    simp only [Multiway.nodes]
    omega
  · simpa only [compact, eq, ite_false] using run_allocation hl hr l r

end RotationBST.SplitTree.Multiway.Join
