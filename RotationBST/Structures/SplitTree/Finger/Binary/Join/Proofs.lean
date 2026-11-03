module

public import RotationBST.Structures.SplitTree.Finger.Binary.Join.Open
public import RotationBST.Structures.SplitTree.Multiway.Join.Left

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Attach a right sibling directly to the maintained minimum-finger view. -/
theorem joinView_rotations (d : Nat) (l r : Multiway) :
    Rotations (openView l r.binary) (binaryView (Join.joinLeft d l r).1.tree).tree (joinViewCost d l r) := by
  cases d with
  | zero => simp only [Join.joinLeft, Join.Promotion.tree, openView, binaryView, BinaryView.tree, comb_append, comb, joinViewCost]; exact .refl
  | succ d =>
    cases r with
    | nil => simp only [Join.joinLeft, Join.Promotion.tree, openView, binaryView, BinaryView.tree, comb_append, comb, joinViewCost, binary]; exact .refl
    | two a b =>
      have child := joinOpen_rotations d l a b.binary
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up <;> simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
          BinaryView.tree, binary, comb_append, comb, joinViewCost] using child
    | three a b c =>
      have child := joinOpen_rotations d l a (.node b.binary c.binary)
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up <;> simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
          BinaryView.tree, binary, comb_append, comb, joinViewCost] using child
    | four a b c e =>
      have start := openView_tail_rotations l
        (show Rotations (.node (.node a.binary b.binary) (.node c.binary e.binary))
          (.node a.binary (.node b.binary (.node c.binary e.binary))) 1 from .step .right .refl)
      have child := joinOpen_rotations d l a (.node b.binary (.node c.binary e.binary))
      have steps := start.append child
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up <;> simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
          BinaryView.tree, binary, comb_append, comb, joinViewCost] using steps

theorem joinOpen_cost (d : Nat) (l r : Multiway) : joinOpenCost d l r ≤ 4 * d := by
  induction d generalizing r with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    cases r with
    | nil => simp [joinOpenCost]
    | two a b => have bound := ih a; simp only [joinOpenCost]; omega
    | three a b c => have bound := ih a; simp only [joinOpenCost]; omega
    | four a b c e =>
      have bound := ih a
      simp only [joinOpenCost]
      split <;> omega

theorem joinView_cost (d : Nat) (l r : Multiway) : joinViewCost d l r ≤ 4 * d := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
    cases r with
    | nil => simp [joinViewCost]
    | two a b => have bound := joinOpen_cost d l a; simp only [joinViewCost]; omega
    | three a b c => have bound := joinOpen_cost d l a; simp only [joinViewCost]; omega
    | four a b c e => have bound := joinOpen_cost d l a; simp only [joinViewCost]; omega

end RotationBST.Arboral.Split.Multiway.Finger
