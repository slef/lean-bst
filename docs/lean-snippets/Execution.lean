inductive Execution : Tree → List Nat → Tree → Nat → Prop where
  | nil {t : Tree} : Execution t [] t 0
  | cons {s t : Tree} {x k : Nat} {xs : List Nat} {u : Tree} {m : Nat} : Access s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)
