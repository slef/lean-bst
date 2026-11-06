module

public import RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Worker.Replay.Requests

/-- The planner's actual concatenated opcodes, with successor states retained.
This omits the two bookkeeping steps charged by the interruptible worker. -/
def program {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) :
    σ → List Nat → List Multifinger.Opcode
  | _, [] => []
  | state, x :: xs =>
      (planner.plan side state x).2 ++ program planner side (planner.plan side state x).1 xs

end RotationBST.Combo.Worker.Replay.Requests
