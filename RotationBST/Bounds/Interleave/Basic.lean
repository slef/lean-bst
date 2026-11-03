module

public import RotationBST.Bounds.Interleave.Definitions.Abstract
import Mathlib.Data.List.Induction

@[expose] public section
namespace RotationBST.Wilber

theorem alternations_append (xs : List Bool) (x : Bool) :
    alternations (xs ++ [x]) = alternations xs + switch xs x := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternations, switch]
  | singleton a => simp [alternations, switch]
  | cons_cons a b xs _ ih =>
    simpa [alternations, switch, List.getLast?_cons_cons, Nat.add_assoc] using (ih b)

theorem regions_append (l n : Nat) (xs ys : List Nat) :
    regions l n (xs ++ ys) = regions l n xs ++ regions l n ys := by
  simp [regions]

theorem left_append (l : Nat) (xs ys : List Nat) :
    leftRequests l (xs ++ ys) = leftRequests l xs ++ leftRequests l ys := by
  simp [leftRequests]

theorem right_append (l : Nat) (xs ys : List Nat) :
    rightRequests l (xs ++ ys) = rightRequests l xs ++ rightRequests l ys := by
  simp [rightRequests]

theorem interleave_nil (t : Tree) : interleave t [] = 0 := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [interleave, regions, alternations, leftRequests, rightRequests, il, ir]

theorem switch_le_one (past : List Bool) (next : Bool) : switch past next ≤ 1 := by
  unfold switch
  split
  · omega
  · split <;> omega

end RotationBST.Wilber
