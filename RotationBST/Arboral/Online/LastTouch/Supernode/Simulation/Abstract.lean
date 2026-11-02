module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Abstract
public import RotationBST.Arboral.Online.Abstract

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Replay the causal stored-state update alongside the geometric algorithm.
Each step sees only the old history, stored state, and current request. -/
def runState (step : Nat → Nat → Finset Point → Finset Nat) :
    Nat → Finset Point → Nested → List Nat → Nested
  | _, _, state, [] => state
  | time, P, state, request :: rest =>
      let keys := step time request P
      runState step (time + 1) (P ∪ row time keys) (nextState state keys) rest

end RotationBST.Arboral.Online.Supernode
