structure Algorithm where
  step : List Nat → Tree → Nat → Tree × Nat
  correct : ∀ past t x, x < t.size →
    Access t (step past t x).1 x (step past t x).2
