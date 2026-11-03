module

public import RotationBST.Structures.SplitTree.Multiway.Join.Defs
public import RotationBST.Structures.SplitTree.Multiway.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Join

/-- The join's counter counts actual rotations, including root overflow. -/
theorem joinRight_rotations (d : Nat) (l r : Multiway) :
    Rotations (.node l.binary r.binary) (joinRight d l r).1.tree.binary (joinRight d l r).2 := by
  induction d generalizing l with
  | zero => exact .refl
  | succ d ih =>
    cases l with
    | nil => exact .refl
    | two a b =>
      have child := ih b
      cases result : joinRight d b r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.tree, binary] at child <;>
          simp only [joinRight, result, Promotion.tree, binary] <;>
          exact .step .right child.inRight
    | three a b c =>
      have child := ih c
      cases result : joinRight d c r with
      | mk up cost =>
        cases up with
        | stay t =>
          simp only [result, Promotion.tree] at child
          simp only [joinRight, result, Promotion.tree, binary]
          exact .step .right (.step (.inRight .right) (child.inRight.inRight))
        | rise x y =>
          simp only [result, Promotion.tree, binary] at child
          simp only [joinRight, result, Promotion.tree, binary]
          have finish := ((child.inRight (l := b.binary)).inRight (l := a.binary)).append (.step .left .refl)
          simpa only [Nat.add_assoc] using Rotations.step Rotate.right (Rotations.step (.inRight .right) finish)
    | four a b c e =>
      have child := ih e
      cases result : joinRight d e r with
      | mk up cost =>
        cases up <;> simp only [result, Promotion.tree, binary] at child <;>
          simp only [joinRight, result, Promotion.tree, binary] <;>
          exact .step .right (.step (.inRight .right) (child.inRight.inRight))

end RotationBST.Geometric.Split.Multiway.Join
