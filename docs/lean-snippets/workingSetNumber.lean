def workingSetNumber (n : Nat) (past : List Nat) (x : Nat) : Nat :=
  if x ∈ past then 1 + (past.reverse.takeWhile (· != x)).eraseDups.length else n
