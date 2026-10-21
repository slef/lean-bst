def Algorithm.runFrom (a : Algorithm) (past : List Nat) (t : Tree) :
    List Nat → Tree × Nat
  | [] => (t, 0)
  | x :: xs =>
      let (u, k) := a.step past t x
      let (v, m) := a.runFrom (past ++ [x]) u xs
      (v, k + m)
