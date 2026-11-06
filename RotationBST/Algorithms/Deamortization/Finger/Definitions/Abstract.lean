module

public import RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

/-- The original source simulation plans request programs causally. The
scheduler may still be executing a prefix of the accumulated programs. -/
structure PreparedOutput (α : Type) where
  source : LabelledCursor.Config α
  history : State α
  requests : List Scheduler.Request

def prepare {α : Type} (p : Simulation.Policy α) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) (c : LabelledCursor.Config α) (s : State α) : List Nat → Option (PreparedOutput α)
  | [] => some ⟨c, s, []⟩
  | key :: keys => (Simulation.run p c s (a.step past c key).1).bind fun first =>
      (prepare p a (past ++ [key]) first.source first.state keys).map fun last =>
        ⟨last.source, last.history, ⟨key, first.instructions⟩ :: last.requests⟩

/-- Both policies are fixed before the input sequence. Planning time follows
the abstract BST model; the output counts every executed pointer instruction. -/
def transform {α : Type} (sourcePolicy : Simulation.Policy α) (scheduler : Scheduler.Policy)
    (a : Simulation.Requests.Algorithm α) (past : List Nat) (c : LabelledCursor.Config α)
    (s : State α) (keys : List Nat) : Option Scheduler.Output :=
  (prepare sourcePolicy a past c s keys).bind fun ready =>
    Scheduler.run scheduler (Scheduler.initial ⟨s.pair.tree, []⟩) ready.requests

end RotationBST.Deamortization.Finger
