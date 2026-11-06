module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests.Results
open LabelledCursor

theorem source_erase {α : Type} (c : Config α) (ops : List Multifinger.Opcode) :
    (sourceRun c ops).map Config.erase = Multifinger.replay ops c.erase :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.source_erase c ops

theorem algorithm_exists (α : Type) : Nonempty (Algorithm α) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.algorithm_exists α

theorem serves {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {key : Nat} (valid : ConfigValid weight c s)
    (search : Serves c ops key final) :
    ∃ out, Simulation.run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      Pointer.Serves s.pair.tree out.state.pair.tree key (1 + out.cost) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.serves policyValid valid search

theorem source_requests_append {α : Type} (a : Algorithm α) (past : List Nat) (c : Config α)
    (xs ys : List Nat) :
    a.runFrom past c (xs ++ ys) =
      let first := a.runFrom past c xs
      let last := a.runFrom (past ++ xs) first.2 ys
      (first.1 ++ last.1, last.2) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.source_requests_append a past c xs ys

theorem run_append {α : Type} (p : Policy α) (a : Algorithm α) (past : List Nat)
    (c : Config α) (s : State α) (xs ys : List Nat) :
    run p a past c s (xs ++ ys) = (run p a past c s xs).bind fun first =>
      (run p a (past ++ xs) first.source first.state ys).map fun last =>
        ⟨last.source, last.state, first.instructions ++ last.instructions⟩ :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.run_append p a past c s xs ys

theorem run_prefix {α : Type} (p : Policy α) (a : Algorithm α) (past : List Nat)
    (c : Config α) (s : State α) (xs ys : List Nat) {out : Output α}
    (completed : run p a past c s (xs ++ ys) = some out) :
    ∃ first, run p a past c s xs = some first ∧ first.instructions <+: out.instructions :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.run_prefix p a past c s xs ys completed

theorem run_spec {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, run p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      Pointer.Execution s.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
      out.cost + out.state.potential ≤ 62 * (a.runFrom past c keys).1.length + s.potential :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.run_spec policyValid a past valid keys validKeys

theorem initialized_run {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (start : State α) (startupCost : Nat),
      ConfigValid weight ⟨.node left key right, cs⟩ start ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨start.pair.tree, []⟩ startupCost ∧
      startupCost + start.potential ≤ 39 * (plug cs (.node left key right)).erase.size ∧
      ∀ (past keys : List Nat),
        (∀ x ∈ keys, x < (plug cs (.node left key right)).erase.size) →
        ∃ out, run p a past ⟨.node left key right, cs⟩ start keys = some out ∧
          out.source = (a.runFrom past ⟨.node left key right, cs⟩ keys).2 ∧
          ConfigValid weight out.source out.state ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          (keys ≠ [] → Pointer.Execution (plug cs (.node left key right)).erase keys
            out.state.pair.tree (startupCost + (keys.length + out.cost))) ∧
          startupCost + keys.length + out.cost + out.state.potential ≤
            39 * (plug cs (.node left key right)).erase.size +
              62 * (keys.length + (a.runFrom past ⟨.node left key right, cs⟩ keys).1.length) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.initialized_run policyValid a positive

theorem serves_recorded {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {key : Nat} (valid : ConfigValid weight c s)
    (search : Serves c ops key final) :
    ∃ out, Simulation.run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      Pointer.Serves s.pair.tree out.state.pair.tree key (1 + out.cost) ∧
      ∃ cut visited, cut ≤ out.instructions.length ∧
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some visited ∧
        visited.key? = some key :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.serves_recorded policyValid valid search

theorem flatten {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) {out : Output α}
    (completed : run p a past c s keys = some out) :
    Simulation.run p c s (a.runFrom past c keys).1 = some out ∧
      sourceRun c (a.runFrom past c keys).1 = some (a.runFrom past c keys).2 :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.flatten policyValid a past valid keys validKeys completed

theorem config_potential_bound {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : s.potential + 20 ≤ 20 * c.tree.erase.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.config_potential_bound valid

theorem interval_work {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, run p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      Pointer.Execution s.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
      keys.length + out.cost ≤ 62 * (keys.length + (a.runFrom past c keys).1.length) +
        20 * c.tree.erase.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.Requests.interval_work policyValid a past valid keys validKeys

end RotationBST.HeavyPath.Finger.History.Simulation.Requests.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Simulation.Requests.Results`: 12 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Simulation.Requests.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
