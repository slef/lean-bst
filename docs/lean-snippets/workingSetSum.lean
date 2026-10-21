def workingSetSum (n : Nat) (past : List Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + (workingSetNumber n past x).log2 +
      workingSetSum n (past ++ [x]) xs
