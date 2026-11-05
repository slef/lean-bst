module

public import RotationBST.Models.Multifinger.Definitions.Abstract

@[expose] public section
namespace RotationBST.Multifinger

inductive Opcode where
  | downLeft | downRight | upLeft | upRight | rotateLeftChild | rotateRightChild
  deriving DecidableEq

/-- The online input names only a finger and one of the six primitive operations. -/
structure Command (fingers : Nat) where
  finger : Fin fingers
  opcode : Opcode

/-- Partial reference semantics of one primitive operation. -/
def perform : Opcode → Pointer.Config → Option Pointer.Config
  | .downLeft, ⟨.node (.node a b) r, cs⟩ => some ⟨.node a b, .left r :: cs⟩
  | .downRight, ⟨.node l (.node a b), cs⟩ => some ⟨.node a b, .right l :: cs⟩
  | .upLeft, ⟨.node a b, .left r :: cs⟩ => some ⟨.node (.node a b) r, cs⟩
  | .upRight, ⟨.node a b, .right l :: cs⟩ => some ⟨.node l (.node a b), cs⟩
  | .rotateLeftChild, ⟨.node a b, .left r :: cs⟩ => some ⟨.node a (.node b r), cs⟩
  | .rotateRightChild, ⟨.node a b, .right l :: cs⟩ => some ⟨.node (.node l a) b, cs⟩
  | _, _ => none

/-- Execute a command at the selected existing key in the reference tree. -/
def Command.Step {fingers : Nat} (s : State fingers) (cmd : Command fingers) (t : State fingers) : Prop :=
  ∃ a b x, a.tree = s.tree ∧ a.key? = some (s.position cmd.finger) ∧
    perform cmd.opcode a = some b ∧ b.key? = some x ∧
    t = ⟨b.tree, Function.update s.position cmd.finger x⟩

/-- A legal command stream, recording the touched key of each operation. -/
inductive Program {fingers : Nat} : State fingers → List (Command fingers) → List Nat → State fingers → Prop where
  | nil {s : State fingers} : Program s [] [] s
  | cons {s t u : State fingers} {cmd : Command fingers} {commands : List (Command fingers)} {touches : List Nat} :
      cmd.Step s t → Program t commands touches u →
      Program s (cmd :: commands) (t.position cmd.finger :: touches) u

end RotationBST.Multifinger
