module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

/-- A source search visits the requested rank at an instruction boundary.
The cursor persists between searches; a visit may occur before any movement. -/
def Serves {α : Type} (c : Config α) (ops : List Multifinger.Opcode)
    (key : Nat) (final : Config α) : Prop :=
  ∃ before after visited, ops = before ++ after ∧ sourceRun c before = some visited ∧
    visited.erase.key? = some key ∧ sourceRun visited after = some final

/-- A source BST algorithm sees past requests, its current cursor and the next
rank. Correctness requires a legal search but permits arbitrary later work. -/
structure Algorithm (α : Type) where
  step : List Nat → Config α → Nat → List Multifinger.Opcode × Config α
  correct : ∀ past c key, c.focus ≠ .nil → key < c.tree.erase.size →
    Serves c (step past c key).1 key (step past c key).2

def Algorithm.runFrom {α : Type} (a : Algorithm α) (past : List Nat) (c : Config α) :
    List Nat → List Multifinger.Opcode × Config α
  | [] => ([], c)
  | key :: keys =>
      let first := a.step past c key
      let last := a.runFrom (past ++ [key]) first.2 keys
      (first.1 ++ last.1, last.2)

/-- Lift the fixed physical instruction policy request by request. Emitted
instructions and source state are carried forward without seeing future keys. -/
def run {α : Type} (p : Policy α) (a : Algorithm α) (past : List Nat)
    (c : Config α) (s : State α) : List Nat → Option (Output α)
  | [] => some ⟨c, s, []⟩
  | key :: keys =>
      (Simulation.run p c s (a.step past c key).1).bind fun first =>
        (run p a (past ++ [key]) first.source first.state keys).map fun last =>
          ⟨last.source, last.state, first.instructions ++ last.instructions⟩

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
