module

public import RotationBST.Arboral.Online.Split.Multiway.Join.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Join

theorem joinRight_balance (d : Nat) {h : Nat} {l r : Multiway}
    (left : Balanced (h + d) l) (right : Balanced h r) :
    (joinRight d l r).1.Valid (h + d) := by
  induction d generalizing l with
  | zero => exact ⟨left, right⟩
  | succ d ih =>
    cases left with
    | @two _ a b ha hb =>
      have child := ih hb
      cases result : joinRight d b r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinRight, result, Promotion.Valid]
        · exact .two ha child
        · exact .three ha child.1 child.2
    | @three _ a b c ha hb hc =>
      have child := ih hc
      cases result : joinRight d c r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinRight, result, Promotion.Valid]
        · exact .three ha hb child
        · exact .four ha hb child.1 child.2
    | @four _ a b c e ha hb hc he =>
      have child := ih he
      cases result : joinRight d e r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.Valid] at child <;>
          simp only [joinRight, result, Promotion.Valid]
        · exact .four ha hb hc child
        · exact ⟨.two ha hb, .three hc child.1 child.2⟩

theorem joinRight_cost (d : Nat) (l r : Multiway) : (joinRight d l r).2 ≤ 3 * d := by
  induction d generalizing l with
  | zero => simp [joinRight]
  | succ d ih =>
    cases l with
    | nil => simp [joinRight]
    | two a b =>
      have bound := ih b
      cases result : joinRight d b r with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinRight, result] <;> omega
    | three a b c =>
      have bound := ih c
      cases result : joinRight d c r with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinRight, result] <;> omega
    | four a b c e =>
      have bound := ih e
      cases result : joinRight d e r with
      | mk up cost => cases up <;> simp only [result] at bound <;> simp only [joinRight, result] <;> omega

end RotationBST.Arboral.Split.Multiway.Join
