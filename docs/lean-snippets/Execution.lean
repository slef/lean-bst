inductive Execution : Tree → List Nat → Tree → Nat → Prop where
  | nil : Execution t [] t 0
  | cons : Access s t x k → Execution t xs u m → Execution s (x :: xs) u (k + m)
