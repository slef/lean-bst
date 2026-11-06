module

public import RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

/-- The complete history invariant at a source cursor. Empty focuses are not
source fingers and cannot execute any of the six labelled instructions. -/
def ConfigValid {α : Type} (weight : α → ℝ) (c : Config α) (s : State α) : Prop :=
  match c.focus with
  | .nil => False
  | .node l key r => Valid weight c.context l key r s

/-- One physical response, including its source cursor and exact trace cost. -/
structure Output (α : Type) where
  source : Config α
  state : State α
  instructions : List Multifinger.Opcode

def Output.cost {α : Type} (out : Output α) : Nat := out.instructions.length

/-- A policy sees only the current source cursor, representation, and opcode. -/
abbrev Policy (α : Type) := Config α → State α → Multifinger.Opcode → Option (Output α)

/-- Every legal instruction preserves the whole state; illegal instructions
are rejected. The potential includes all nested payload occurrences. -/
def PolicyValid {α : Type} (weight : α → ℝ) (policy : Policy α) : Prop :=
  ∀ c s op, ConfigValid weight c s →
    match perform op c with
    | none => policy c s op = none
    | some next => ∃ out, policy c s op = some out ∧ out.source = next ∧
        ConfigValid weight out.source out.state ∧
        Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
        out.cost + out.state.potential ≤ 62 + s.potential

/-- The same causal policy retains a logarithmic worst-case response bound
in addition to its global potential inequality. -/
def PolicyBounded {α : Type} (weight : α → ℝ) (policy : Policy α) : Prop :=
  PolicyValid weight policy ∧ ∀ c s op out, ConfigValid weight c s →
    policy c s op = some out → (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size

/-- A bounded causal policy whose actual emitted program retains a structural
key-depth certificate at every physical interruption. -/
def PolicyWithin {α : Type} (weight : α → ℝ) (policy : Policy α) : Prop :=
  PolicyBounded weight policy ∧ ∀ c s op out, ConfigValid weight c s →
    policy c s op = some out → ∀ cut, ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x, Tree.depth middle.tree x ≤ 16 * Tree.depth s.pair.tree x + 96

/-- Execute a finite source instruction stream, rejecting the first illegal
instruction. This is the reference semantics, independent of a policy. -/
def sourceRun {α : Type} (c : Config α) : List Multifinger.Opcode → Option (Config α)
  | [] => some c
  | op :: ops => (perform op c).bind (fun next => sourceRun next ops)

/-- Execute the same fixed policy at every instruction. Only accumulated
physical trace cost is added; the final state carries its remaining credit. -/
def run {α : Type} (p : Policy α) (c : Config α) (s : State α) :
    List Multifinger.Opcode → Option (Output α)
  | [] => some ⟨c, s, []⟩
  | op :: ops => (p c s op).bind fun first =>
      (run p first.source first.state ops).map fun last =>
        ⟨last.source, last.state, first.instructions ++ last.instructions⟩

end RotationBST.HeavyPath.Finger.History.Simulation
