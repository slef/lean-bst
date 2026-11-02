module

public import RotationBST.Online.Abstract

@[expose] public section

namespace RotationBST

/-- First access has working-set number `n`; otherwise count distinct keys
since its last access, plus one. -/
def workingSetNumber (n : Nat) (past : List Nat) (x : Nat) : Nat :=
  if x ∈ past then 1 + (past.reverse.takeWhile (· != x)).eraseDups.length else n

def workingSetSum (n : Nat) (past : List Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + (workingSetNumber n past x).log2 +
      workingSetSum n (past ++ [x]) xs

/-- Total working-set bound, with an initial-tree allowance. -/
def HasWorkingSetBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
    a.cost t xs ≤ C * workingSetSum t.size [] xs +
      D * t.size * (1 + t.size.log2)

end RotationBST
