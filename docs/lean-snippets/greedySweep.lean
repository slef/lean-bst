def greedySweep (time request : Nat) (P : Finset Point) : Finset Nat :=
  insert request ((P.filter (Visible P time request)).image Prod.fst)
