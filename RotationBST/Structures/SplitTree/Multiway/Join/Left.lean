module

public import RotationBST.Structures.SplitTree.Multiway.Join.Balance

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Join

theorem joinLeft_rotations (d : Nat) (l r : Multiway) :
    Rotations (.node l.binary r.binary) (joinLeft d l r).1.tree.binary (joinLeft d l r).2 := by
  induction d generalizing r with
  | zero => exact .refl
  | succ d ih =>
    cases r with
    | nil => exact .refl
    | two a b =>
      have child := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up with
        | stay t =>
          simp only [result, Promotion.tree] at child
          simp only [joinLeft, result, Promotion.tree, binary]
          exact .step .left child.inLeft
        | rise x y =>
          simp only [result, Promotion.tree, binary] at child
          simp only [joinLeft, result, Promotion.tree, binary]
          have finish := (child.inLeft (r := b.binary)).append (.step .right .refl)
          simpa only [Nat.add_assoc] using Rotations.step Rotate.left finish
    | three a b c =>
      have child := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.tree, binary] at child <;>
          simp only [joinLeft, result, Promotion.tree, binary] <;>
          exact .step .left child.inLeft
    | four a b c e =>
      have child := ih a
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up with
        | stay t =>
          simp only [result, Promotion.tree] at child
          simp only [joinLeft, result, Promotion.tree, binary]
          exact .step .left (.step (.inLeft .left) child.inLeft.inLeft)
        | rise x y =>
          simp only [result, Promotion.tree, binary] at child
          simp only [joinLeft, result, Promotion.tree, binary]
          have finish := ((child.inLeft (r := b.binary)).inLeft (r := .node c.binary e.binary)).append
            (.step (.inLeft .right) .refl)
          simpa only [Nat.add_assoc] using Rotations.step Rotate.left (Rotations.step (.inLeft .left) finish)

theorem joinLeft_balance (d : Nat) {h : Nat} {l r : Multiway}
    (left : Balanced h l) (right : Balanced (h + d) r) :
    (joinLeft d l r).1.Valid (h + d) := by
  induction d generalizing r with
  | zero => exact ⟨left, right⟩
  | succ d ih =>
    cases right with
    | @two _ a b ha hb =>
      have child := ih ha
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinLeft, result, Promotion.Valid]
        · exact .two child hb
        · exact .three child.1 child.2 hb
    | @three _ a b c ha hb hc =>
      have child := ih ha
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinLeft, result, Promotion.Valid]
        · exact .three child hb hc
        · exact .four child.1 child.2 hb hc
    | @four _ a b c e ha hb hc he =>
      have child := ih ha
      cases result : joinLeft d l a with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinLeft, result, Promotion.Valid]
        · exact .four child hb hc he
        · exact ⟨.three child.1 child.2 hb, .two hc he⟩

theorem joinLeft_cost (d : Nat) (l r : Multiway) : (joinLeft d l r).2 ≤ 3 * d := by
  induction d generalizing r with
  | zero => simp [joinLeft]
  | succ d ih =>
    cases r with
    | nil => simp [joinLeft]
    | two a b =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinLeft, result] <;> omega
    | three a b c =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinLeft, result] <;> omega
    | four a b c e =>
      have bound := ih a
      cases result : joinLeft d l a with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinLeft, result] <;> omega

end RotationBST.SplitTree.Multiway.Join
