module

public import RotationBST.Online.Abstract
public import RotationBST.Pointer.Machine.Abstract

@[expose] public section

namespace RotationBST.Pointer.Lazy.Online

/-- The real pointer tree and the virtual rotation-model tree, related by the
rotations postponed so far. This state contains no future requests. -/
structure State where
  current : Tree
  virtual : Tree
  pending : Nat
  certificate : Rotations current virtual pending

def initial (t : Tree) : State := ⟨t, t, 0, .refl⟩

/-- One causal simulation step, with pending work carried as a potential. -/
def Transition (a : Algorithm) (past : List Nat) (s : State) (x : Nat)
    (result : State × Nat) : Prop :=
  Pointer.Serves s.current result.1.current x result.2 ∧
  result.1.virtual = (a.step past s.virtual x).1 ∧
  result.2 + 32 * result.1.pending ≤
    32 * (s.pending + (a.step past s.virtual x).2) + 17

end RotationBST.Pointer.Lazy.Online
