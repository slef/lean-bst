module

public import RotationBST.Bounds.Interleave.Basic

import Mathlib.Data.List.Induction

@[expose] public section
namespace RotationBST.Wilber

/-- Concatenation retains all switches inside either block; its boundary may
add one more switch. -/
theorem alternations_superadditive (xs ys : List Bool) :
    alternations xs + alternations ys ≤ alternations (xs ++ ys) := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternations]
  | singleton x =>
    cases ys with
    | nil => simp [alternations]
    | cons y ys => simp only [List.singleton_append, alternations]; omega
  | cons_cons a b xs _ ih =>
    simp only [List.cons_append, alternations]
    have tail := ih b
    simp only [List.cons_append] at tail
    omega

/-- Every subtree retains its within-block alternations when sequences are
concatenated. This supports arbitrarily many repetitions of a hard period. -/
theorem interleave_superadditive (t : Tree) (xs ys : List Nat) :
    interleave t xs + interleave t ys ≤ interleave t (xs ++ ys) := by
  induction t generalizing xs ys with
  | nil => simp [interleave]
  | node l r il ir =>
    have root := alternations_superadditive (regions l.size (l.size + 1 + r.size) xs)
      (regions l.size (l.size + 1 + r.size) ys)
    have left := il (leftRequests l.size xs) (leftRequests l.size ys)
    have right := ir (rightRequests l.size xs) (rightRequests l.size ys)
    simp only [interleave, regions_append, left_append, right_append]
    omega

end RotationBST.Wilber
