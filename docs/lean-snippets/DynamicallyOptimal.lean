def DynamicallyOptimal (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs u k, Execution t xs u k →
    a.cost t xs ≤ C * k + D * t.size
