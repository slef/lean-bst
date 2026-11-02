def ASS (P : Finset Point) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a.1 ≠ b.1 → a.2 ≠ b.2 →
    ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ Rectangle a b p
