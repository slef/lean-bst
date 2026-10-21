def Access (s t : Tree) (x k : Nat) : Prop :=
  Rotations s t k ∧ match t with
    | .nil => False
    | .node l _ => l.size = x
