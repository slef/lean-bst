module

public import RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract
public import RotationBST.Models.Region.Fringe
public import RotationBST.Models.Rotation.Rotations

@[expose] public section
namespace RotationBST.Region
open Pointer.Lazy.Skeleton

theorem shape_size (s : Region) : (shape s).size = s.size := by
  induction s with
  | hole t => rfl
  | node l r il ir => simp only [shape, Tree.size, size, il, ir]

/-- Each auxiliary rotation is one genuine BST rotation, leaving every attached
fringe subtree intact. This is independent of the sizes of those subtrees. -/
theorem lift_rotate {a b : Tree} (rotation : Rotate a b) (s : Region) (hs : shape s = a) :
    ∃ u : Region, shape u = b ∧ s.fringe = u.fringe ∧ Rotate s.tree u.tree := by
  induction rotation generalizing s with
  | right =>
    cases s with
    | hole t => simp [shape] at hs
    | node l r =>
      cases l with
      | hole t => simp [shape] at hs
      | node a b =>
        simp only [shape, Tree.node.injEq] at hs
        exact ⟨.node a (.node b r), by simp only [shape, hs], by simp [fringe, List.append_assoc], .right⟩
  | left =>
    cases s with
    | hole t => simp [shape] at hs
    | node l r =>
      cases r with
      | hole t => simp [shape] at hs
      | node b c =>
        simp only [shape, Tree.node.injEq] at hs
        exact ⟨.node (.node l b) c, by simp only [shape, hs], by simp [fringe, List.append_assoc], .left⟩
  | inLeft _ ih =>
    cases s with
    | hole t => simp [shape] at hs
    | node l r =>
      obtain ⟨hl, hr⟩ := Tree.node.inj hs
      obtain ⟨u, hu, hf, ht⟩ := ih l hl
      exact ⟨.node u r, by simp [shape, hu, hr], by simp [fringe, hf], .inLeft ht⟩
  | inRight _ ih =>
    cases s with
    | hole t => simp [shape] at hs
    | node l r =>
      obtain ⟨hl, hr⟩ := Tree.node.inj hs
      obtain ⟨u, hu, hf, ht⟩ := ih r hr
      exact ⟨.node l u, by simp [shape, hl, hu], by simp [fringe, hf], .inRight ht⟩

theorem lift_rotations {a b : Tree} {cost : Nat} (rotations : Rotations a b cost)
    (s : Region) (hs : shape s = a) :
    ∃ u : Region, shape u = b ∧ s.fringe = u.fringe ∧ Rotations s.tree u.tree cost := by
  induction rotations generalizing s with
  | refl => exact ⟨s, hs, rfl, .refl⟩
  | step first _ ih =>
    obtain ⟨v, hv, hf, hr⟩ := lift_rotate first s hs
    obtain ⟨u, hu, hfu, hru⟩ := ih v hv
    exact ⟨u, hu, hf.trans hfu, .step hr hru⟩

end RotationBST.Region
