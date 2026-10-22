structure StatefulAlgorithm (σ : Type) where
  init : Tree → σ
  step : σ → Tree → Nat → σ × Tree × Nat
  correct : ∀ q t x, x < t.size →
    Access t (step q t x).2.1 x (step q t x).2.2
