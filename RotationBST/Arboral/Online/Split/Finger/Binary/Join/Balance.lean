module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Join.Proofs
public import RotationBST.Arboral.Online.Split.Multiway.Join.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

theorem attachRight_rotations (hl hr : Nat) (l r : Multiway) :
    Rotations (openView l r.binary) (binaryView (attachRight hl hr l r).tree).tree
      (attachRight hl hr l r).cost := by
  simpa only [attachRight, Join.finish_tree] using joinView_rotations (hr - hl) l r

theorem attachRight_open (hl hr : Nat) (l r : Multiway) (rest : Tree) :
    Rotations (openView l (.node r.binary rest)) (openView (attachRight hl hr l r).tree rest)
      (joinOpenCost (hr - hl) l r) := by
  simpa only [attachRight, Join.finish_tree] using joinOpen_rotations (hr - hl) l r rest

theorem attachRight_balance {hl hr : Nat} {l r : Multiway}
    (left : Balanced hl l) (right : Balanced hr r) (ordered : hl ≤ hr) :
    Balanced (attachRight hl hr l r).height (attachRight hl hr l r).tree ∧
      hr ≤ (attachRight hl hr l r).height ∧ (attachRight hl hr l r).height ≤ hr + 1 := by
  have taller : Balanced (hl + (hr - hl)) r := by
    rw [show hl + (hr - hl) = hr by omega]; exact right
  have result := Join.finish_balance (Join.joinLeft_balance (hr - hl) left taller)
  rw [show hl + (hr - hl) = hr by omega] at result
  exact result

theorem attachRight_cost (hl hr : Nat) (l r : Multiway) :
    (attachRight hl hr l r).cost ≤ 4 * (hr - hl) := joinView_cost _ _ _

/-- With a one-level deficit and a non-full sibling, the enclosing separator is
absorbed without replacing the lost level. Exactly one enclosing node disappears. -/
theorem attachRight_two_deficit (h : Nat) (focus a b : Multiway) :
    (attachRight h (h + 1) focus (.two a b)).tree = .three focus a b ∧
      (attachRight h (h + 1) focus (.two a b)).height = h + 1 ∧
      (attachRight h (h + 1) focus (.two a b)).tree.nodes + 1 = (Multiway.two focus (.two a b)).nodes := by
  simp [attachRight, Join.joinLeft, Join.finish, nodes]
  omega

theorem attachRight_three_deficit (h : Nat) (focus a b c : Multiway) :
    (attachRight h (h + 1) focus (.three a b c)).tree = .four focus a b c ∧
      (attachRight h (h + 1) focus (.three a b c)).height = h + 1 ∧
      (attachRight h (h + 1) focus (.three a b c)).tree.nodes + 1 = (Multiway.two focus (.three a b c)).nodes := by
  simp [attachRight, Join.joinLeft, Join.finish, nodes]
  omega

/-- A full sibling restores the parent height, ending deficit propagation. -/
theorem attachRight_four_deficit (h : Nat) (focus a b c d : Multiway) :
    (attachRight h (h + 1) focus (.four a b c d)).tree = .two (.three focus a b) (.two c d) ∧
      (attachRight h (h + 1) focus (.four a b c d)).height = h + 2 := by
  simp [attachRight, Join.joinLeft, Join.finish]

/-- A non-full taller sibling absorbs the promoted separator at its own height. -/
theorem attachRight_taller_two {hl hr : Nat} (taller : hl < hr) (focus a b : Multiway) :
    (attachRight hl hr focus (.two a b)).height = hr := by
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hr - hl ≠ 0 by omega)
  simp only [attachRight, diff, Join.joinLeft]
  cases result : Join.joinLeft d focus a with
  | mk up cost => cases up <;> rfl

theorem attachRight_taller_three {hl hr : Nat} (taller : hl < hr) (focus a b c : Multiway) :
    (attachRight hl hr focus (.three a b c)).height = hr := by
  obtain ⟨d, diff⟩ := Nat.exists_eq_succ_of_ne_zero (show hr - hl ≠ 0 by omega)
  simp only [attachRight, diff, Join.joinLeft]
  cases result : Join.joinLeft d focus a with
  | mk up cost => cases up <;> rfl

end RotationBST.Arboral.Split.Multiway.Finger
