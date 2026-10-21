def Algorithm.cost (a : Algorithm) (t : Tree) (xs : List Nat) : Nat :=
  (a.runFrom [] t xs).2
