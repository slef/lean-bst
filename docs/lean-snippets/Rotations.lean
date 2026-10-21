inductive Rotations : Tree → Tree → Nat → Prop where
  | refl : Rotations t t 0
  | step : Rotate s t → Rotations t u k → Rotations s u (k + 1)
