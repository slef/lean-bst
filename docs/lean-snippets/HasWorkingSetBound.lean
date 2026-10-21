def HasWorkingSetBound (a : Algorithm) : Prop :=
  ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
    a.cost t xs ≤ C * workingSetSum t.size [] xs +
      D * t.size * (1 + t.size.log2)
