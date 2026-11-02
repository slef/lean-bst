inductive Rotations : Tree → Tree → Nat → Prop where
  | refl {t : Tree} : Rotations t t 0
  | step {s t u : Tree} {k : Nat} : Rotate s t → Rotations t u k → Rotations s u (k + 1)
