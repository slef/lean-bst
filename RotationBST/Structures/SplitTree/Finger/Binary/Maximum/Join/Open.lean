module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

theorem leftComb_rotations (xs : List Tree) {s u : Tree} {cost : Nat}
    (steps : Rotations s u cost) : Rotations (leftComb xs s) (leftComb xs u) cost := by
  induction xs with
  | nil => exact steps
  | cons a xs ih => exact ih.inLeft

theorem maximumOpenView_tail_rotations (t : Multiway) {s u : Tree} {cost : Nat}
    (steps : Rotations s u cost) :
    Rotations (maximumOpenView t s) (maximumOpenView t u) cost :=
  leftComb_rotations (maximumView t).spine steps.inLeft

theorem maximumJoinOpen_rotations (d : Nat) (l r : Multiway) (rest : Tree) :
    Rotations (maximumOpenView r (.node rest l.binary))
      (maximumOpenView (Join.joinRight d l r).1.tree rest) (maximumJoinOpenCost d l r) := by
  induction d generalizing l rest with
  | zero => simp only [Join.joinRight, Join.Promotion.tree, maximumOpenView, maximumView, leftComb_append, leftComb, maximumJoinOpenCost]; exact .refl
  | succ d ih =>
    cases l with
    | nil => simp only [Join.joinRight, Join.Promotion.tree, maximumOpenView, maximumView, leftComb_append, leftComb, maximumJoinOpenCost, binary]; exact .refl
    | two a b =>
      have start := maximumOpenView_tail_rotations r
        (show Rotations (.node rest (.node a.binary b.binary)) (.node (.node rest a.binary) b.binary) 1 from .step .left .refl)
      have child := ih b (.node rest a.binary)
      have steps := start.append child
      cases result : Join.joinRight d b r with
      | mk up cost =>
        cases up <;> simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
          binary, leftComb_append, leftComb, maximumJoinOpenCost] using steps
    | three a b c =>
      have start := maximumOpenView_tail_rotations r
        (show Rotations (.node rest (.node a.binary (.node b.binary c.binary)))
          (.node (.node (.node rest a.binary) b.binary) c.binary) 2 from
          .step .left (.step .left .refl))
      have child := ih c (.node (.node rest a.binary) b.binary)
      have steps := start.append child
      cases result : Join.joinRight d c r with
      | mk up cost =>
        cases up <;> simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
          binary, leftComb_append, leftComb, maximumJoinOpenCost] using steps
    | four a b c e =>
      have start := maximumOpenView_tail_rotations r
        (show Rotations (.node rest (.node (.node a.binary b.binary) (.node c.binary e.binary)))
          (.node (.node (.node (.node rest a.binary) b.binary) c.binary) e.binary) 3 from
          .step .left (.step .left (.step (.inLeft (.inLeft .left)) .refl)))
      have child := ih e (.node (.node (.node rest a.binary) b.binary) c.binary)
      have steps := start.append child
      cases result : Join.joinRight d e r with
      | mk up cost =>
        cases up with
        | stay t =>
          simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
            binary, leftComb_append, leftComb, maximumJoinOpenCost] using steps
        | rise x y =>
          have finish : Rotations
              (maximumOpenView (.two x y) (.node (.node (.node rest a.binary) b.binary) c.binary))
              (maximumOpenView (.two (.two a b) (.three c x y)) rest) 1 := by
            simp only [maximumOpenView, maximumView, binary, leftComb_append, leftComb]
            exact leftComb_rotations (maximumView y).spine
              (.step (.inLeft (.inLeft (.inLeft .right))) .refl)
          simp only [result, Join.Promotion.tree] at steps
          simpa only [Join.joinRight, result, Join.Promotion.tree, maximumJoinOpenCost, binary] using steps.append finish

end RotationBST.Arboral.Split.Multiway.Finger
