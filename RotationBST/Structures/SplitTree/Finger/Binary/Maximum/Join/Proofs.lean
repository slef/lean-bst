module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Open
public import RotationBST.Structures.SplitTree.Multiway.Join.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

theorem maximumJoinView_rotations (d : Nat) (l r : Multiway) :
    Rotations (maximumOpenView r l.binary) (maximumView (Join.joinRight d l r).1.tree).tree
      (maximumJoinViewCost d l r) := by
  cases d with
  | zero => simp only [Join.joinRight, Join.Promotion.tree, maximumOpenView, maximumView, MaximumView.tree, leftComb_append, leftComb, maximumJoinViewCost]; exact .refl
  | succ d =>
    cases l with
    | nil => simp only [Join.joinRight, Join.Promotion.tree, maximumOpenView, maximumView, MaximumView.tree, leftComb_append, leftComb, maximumJoinViewCost, binary]; exact .refl
    | two a b =>
      have child := maximumJoinOpen_rotations d b r a.binary
      cases result : Join.joinRight d b r with
      | mk up cost =>
        cases up <;> simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
          MaximumView.tree, binary, leftComb_append, leftComb, maximumJoinViewCost] using child
    | three a b c =>
      have start := maximumOpenView_tail_rotations r
        (show Rotations (.node a.binary (.node b.binary c.binary))
          (.node (.node a.binary b.binary) c.binary) 1 from .step .left .refl)
      have child := maximumJoinOpen_rotations d c r (.node a.binary b.binary)
      have steps := start.append child
      cases result : Join.joinRight d c r with
      | mk up cost =>
        cases up <;> simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
          MaximumView.tree, binary, leftComb_append, leftComb, maximumJoinViewCost] using steps
    | four a b c e =>
      have start := maximumOpenView_tail_rotations r
        (show Rotations (.node (.node a.binary b.binary) (.node c.binary e.binary))
          (.node (.node (.node a.binary b.binary) c.binary) e.binary) 1 from .step .left .refl)
      have child := maximumJoinOpen_rotations d e r (.node (.node a.binary b.binary) c.binary)
      have steps := start.append child
      cases result : Join.joinRight d e r with
      | mk up cost =>
        cases up <;> simpa only [Join.joinRight, result, Join.Promotion.tree, maximumOpenView, maximumView,
          MaximumView.tree, binary, leftComb_append, leftComb, maximumJoinViewCost] using steps

theorem maximumJoinOpen_cost (d : Nat) (l r : Multiway) : maximumJoinOpenCost d l r ≤ 4 * d := by
  induction d generalizing l with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    cases l with
    | nil => simp [maximumJoinOpenCost]
    | two a b => have bound := ih b; simp only [maximumJoinOpenCost]; omega
    | three a b c => have bound := ih c; simp only [maximumJoinOpenCost]; omega
    | four a b c e =>
      have bound := ih e
      simp only [maximumJoinOpenCost]
      split <;> omega

theorem maximumJoinView_cost (d : Nat) (l r : Multiway) : maximumJoinViewCost d l r ≤ 4 * d := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
    cases l with
    | nil => simp [maximumJoinViewCost]
    | two a b => have bound := maximumJoinOpen_cost d b r; simp only [maximumJoinViewCost]; omega
    | three a b c => have bound := maximumJoinOpen_cost d c r; simp only [maximumJoinViewCost]; omega
    | four a b c e => have bound := maximumJoinOpen_cost d e r; simp only [maximumJoinViewCost]; omega

theorem attachLeft_rotations (hf hs : Nat) (focus sibling : Multiway) :
    Rotations (maximumOpenView focus sibling.binary) (maximumView (attachLeft hf hs focus sibling).tree).tree
      (attachLeft hf hs focus sibling).cost := by
  simpa only [attachLeft, Join.finish_tree] using maximumJoinView_rotations (hs - hf) sibling focus

theorem attachLeft_open (hf hs : Nat) (focus sibling : Multiway) (rest : Tree) :
    Rotations (maximumOpenView focus (.node rest sibling.binary))
      (maximumOpenView (attachLeft hf hs focus sibling).tree rest)
      (maximumJoinOpenCost (hs - hf) sibling focus) := by
  simpa only [attachLeft, Join.finish_tree] using maximumJoinOpen_rotations (hs - hf) sibling focus rest

theorem attachLeft_balance {hf hs : Nat} {focus sibling : Multiway}
    (focused : Balanced hf focus) (retained : Balanced hs sibling) (ordered : hf ≤ hs) :
    Balanced (attachLeft hf hs focus sibling).height (attachLeft hf hs focus sibling).tree ∧
      hs ≤ (attachLeft hf hs focus sibling).height ∧ (attachLeft hf hs focus sibling).height ≤ hs + 1 := by
  have taller : Balanced (hf + (hs - hf)) sibling := by
    rw [show hf + (hs - hf) = hs by omega]; exact retained
  have result := Join.finish_balance (Join.joinRight_balance (hs - hf) taller focused)
  rw [show hf + (hs - hf) = hs by omega] at result
  exact result

theorem attachLeft_cost (hf hs : Nat) (focus sibling : Multiway) :
    (attachLeft hf hs focus sibling).cost ≤ 4 * (hs - hf) := maximumJoinView_cost _ _ _

/-- A non-full taller sibling absorbs the promoted separator at its own height. -/
theorem attachLeft_taller_two {hl hr : Nat} (taller : hl < hr) (focus a b : Multiway) :
    (attachLeft hl hr focus (.two a b)).height = hr := by
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hr - hl ≠ 0 by omega)
  simp only [attachLeft, diff, Join.joinRight]
  cases result : Join.joinRight d b focus with
  | mk up cost => cases up <;> rfl

theorem attachLeft_taller_three {hl hr : Nat} (taller : hl < hr) (focus a b c : Multiway) :
    (attachLeft hl hr focus (.three a b c)).height = hr := by
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hr - hl ≠ 0 by omega)
  simp only [attachLeft, diff, Join.joinRight]
  cases result : Join.joinRight d c focus with
  | mk up cost => cases up <;> rfl

end RotationBST.Arboral.Split.Multiway.Finger
