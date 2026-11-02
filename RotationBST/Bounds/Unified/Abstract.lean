module

public import RotationBST.Bounds.Abstract

@[expose] public section

namespace RotationBST.Splay

/-- One request's best frequency, static-finger, or working-set logarithm. -/
noncomputable def unifiedCharge (n f : Nat) (original past : List Nat) (x : Nat) : ℝ :=
  1 + min (Real.logb 2 (workingSetNumber n past x))
    (min (Real.logb 2 ((original.length : ℝ) / original.count x))
      (Real.logb 2 (Nat.dist x f + 1 : Nat)))

/-- Frequencies use the entire sequence, while recency uses only the prefix. -/
noncomputable def unifiedSum (n f : Nat) (original : List Nat) : List Nat → List Nat → ℝ
  | _, [] => 0
  | past, x :: xs => unifiedCharge n f original past x + unifiedSum n f original (past ++ [x]) xs

end RotationBST.Splay
