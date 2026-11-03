module

public import RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Rotations

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Editing the retained remainder does not move or rebuild the finger prefix. -/
theorem openView_tail_rotations (t : Multiway) {s u : Tree} {cost : Nat} (steps : Rotations s u cost) :
    Rotations (openView t s) (openView t u) cost :=
  comb_rotations (binaryView t).spine steps.inRight

theorem joinOpen_rotations (d : Nat) (l r : Multiway) (rest : Tree) :
    Rotations (openView l (.node r.binary rest))
      (openView (Join.joinLeft d l r).1.tree rest) (joinOpenCost d l r) := by
  induction d generalizing r rest with
  | zero => simp only [Join.joinLeft, Join.Promotion.tree, openView, binaryView, comb_append, comb, joinOpenCost]; exact .refl
  | succ d ih =>
    cases r with
    | nil => simp only [Join.joinLeft, Join.Promotion.tree, openView, binaryView, comb_append, comb, joinOpenCost, binary]; exact .refl
    | two a b =>
      have start := openView_tail_rotations l
        (show Rotations (.node (.node a.binary b.binary) rest) (.node a.binary (.node b.binary rest)) 1 from .step .right .refl)
      have child := ih a (.node b.binary rest)
      have steps := start.append child
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up <;> simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
          binary, comb_append, comb, joinOpenCost] using steps
    | three a b c =>
      have start := openView_tail_rotations l
        (show Rotations (.node (.node a.binary (.node b.binary c.binary)) rest)
          (.node a.binary (.node b.binary (.node c.binary rest))) 2 from
          .step .right (.step (.inRight .right) .refl))
      have child := ih a (.node b.binary (.node c.binary rest))
      have steps := start.append child
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up <;> simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
          binary, comb_append, comb, joinOpenCost] using steps
    | four a b c e =>
      have start := openView_tail_rotations l
        (show Rotations (.node (.node (.node a.binary b.binary) (.node c.binary e.binary)) rest)
          (.node a.binary (.node b.binary (.node c.binary (.node e.binary rest)))) 3 from
          .step .right (.step (.inRight .right) (.step .right .refl)))
      have child := ih a (.node b.binary (.node c.binary (.node e.binary rest)))
      have steps := start.append child
      cases result : Join.joinLeft d l a with
      | mk up cost =>
        cases up with
        | stay t =>
          simpa only [Join.joinLeft, result, Join.Promotion.tree, openView, binaryView,
            binary, comb_append, comb, joinOpenCost] using steps
        | rise x y =>
          have finish : Rotations
              (openView (.two x y) (.node b.binary (.node c.binary (.node e.binary rest))))
              (openView (.two (.three x y b) (.two c e)) rest) 1 := by
            simp only [openView, binaryView, binary, comb_append, comb]
            exact comb_rotations (binaryView x).spine
              (.step (.inRight (.inRight (.inRight .left))) .refl)
          simp only [result, Join.Promotion.tree] at steps
          simpa only [Join.joinLeft, result, Join.Promotion.tree, joinOpenCost, binary] using steps.append finish

end RotationBST.Arboral.Split.Multiway.Finger
