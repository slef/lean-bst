module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Finger.AbstractBridge

@[expose] public section
namespace RotationBST.Deamortization.Finger.Results
open HeavyPath.Finger.History

theorem initial_valid {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p)
    {c : LabelledCursor.Config α} {s : State α} (valid : Simulation.ConfigValid (fun _ => 1) c s)
    {budget : Nat} (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget) :
    Scheduler.Valid budget (Scheduler.initial ⟨s.pair.tree, []⟩) :=
  RotationBST.Deamortization.Finger.initial_valid bounded valid budgetBound

theorem prepare_spec {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s) {budget : Nat}
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, prepare p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      Simulation.ConfigValid (fun _ => 1) out.source out.history ∧ out.requests.map Scheduler.Request.target = keys ∧
      Scheduler.PreparedStream budget ⟨s.pair.tree, []⟩ out.requests ⟨out.history.pair.tree, []⟩ ∧
      (out.requests.map (fun request => request.instructions.length)).sum + out.history.potential ≤
        62 * (a.runFrom past c keys).1.length + s.potential :=
  RotationBST.Deamortization.Finger.prepare_spec bounded a past valid budgetBound keys validKeys

theorem prepare_append {α : Type} (p : Simulation.Policy α) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) (c : LabelledCursor.Config α) (s : State α) (xs ys : List Nat) :
    prepare p a past c s (xs ++ ys) = (prepare p a past c s xs).bind fun first =>
      (prepare p a (past ++ xs) first.source first.history ys).map fun last =>
        ⟨last.source, last.history, first.requests ++ last.requests⟩ :=
  RotationBST.Deamortization.Finger.prepare_append p a past c s xs ys

theorem prepare_prefix {α : Type} (p : Simulation.Policy α) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) (c : LabelledCursor.Config α) (s : State α) (xs ys : List Nat)
    {out : PreparedOutput α} (completed : prepare p a past c s (xs ++ ys) = some out) :
    ∃ first, prepare p a past c s xs = some first ∧ first.requests <+: out.requests :=
  RotationBST.Deamortization.Finger.prepare_prefix p a past c s xs ys completed

theorem transform_prefix {α : Type} (sourcePolicy : Simulation.Policy α) (scheduler : Scheduler.Policy)
    (a : Simulation.Requests.Algorithm α) (past : List Nat) (c : LabelledCursor.Config α)
    (s : State α) (xs ys : List Nat) {out : Scheduler.Output}
    (completed : transform sourcePolicy scheduler a past c s (xs ++ ys) = some out) :
    ∃ first, transform sourcePolicy scheduler a past c s xs = some first ∧
      first.instructions <+: out.instructions ∧ first.costs <+: out.costs :=
  RotationBST.Deamortization.Finger.transform_prefix sourcePolicy scheduler a past c s xs ys completed

theorem transform_spec {α : Type} {sourcePolicy : Simulation.Policy α} {scheduler : Scheduler.Policy}
    (bounded : Simulation.PolicyBounded (fun _ => 1) sourcePolicy) {budget : Nat}
    (schedulerValid : Scheduler.PolicyValid budget scheduler) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ (out : Scheduler.Output) (planned : PreparedOutput α),
      prepare sourcePolicy a past c s keys = some planned ∧
      transform sourcePolicy scheduler a past c s keys = some out ∧
      out.state.planned = ⟨planned.history.pair.tree, []⟩ ∧ Scheduler.Valid budget out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
      Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
        (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.instructions.length + 5 * out.state.pending.length + 5 * planned.history.potential ≤
        310 * (a.runFrom past c keys).1.length + 5 * s.potential ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      ∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget :=
  RotationBST.Deamortization.Finger.transform_spec bounded schedulerValid a past valid budgetBound keys validKeys

theorem initialized_transform {α : Type} (a : Simulation.Requests.Algorithm α)
    (c : LabelledCursor.Config α) (live : c.focus ≠ .nil) :
    ∃ (sourcePolicy : Simulation.Policy α) (scheduler : Scheduler.Policy) (budget : Nat)
      (s : State α) (startup : Nat),
      Simulation.PolicyBounded (fun _ => 1) sourcePolicy ∧ Scheduler.PolicyValid budget scheduler ∧
      Simulation.ConfigValid (fun _ => 1) c s ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨s.pair.tree, []⟩ startup ∧ startup ≤ 16 * c.tree.erase.size ∧
      (budget : ℝ) < 50 + 39 * Real.logb 2 c.tree.erase.size ∧
      ∀ (past keys : List Nat), (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, transform sourcePolicy scheduler a past c s keys = some out ∧
          Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
          Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          startup + keys.length + out.instructions.length ≤
            131 * c.tree.erase.size + keys.length + 310 * (a.runFrom past c keys).1.length ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size :=
  RotationBST.Deamortization.Finger.initialized_transform a c live

theorem prepare_excess {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s) {budget : Nat}
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, prepare p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      Simulation.ConfigValid (fun _ => 1) out.source out.history ∧ out.requests.map Scheduler.Request.target = keys ∧
      Scheduler.PreparedStream budget ⟨s.pair.tree, []⟩ out.requests ⟨out.history.pair.tree, []⟩ ∧
      (out.requests.map (fun request => request.instructions.length)).sum + Simulation.Minimum.excess (fun _ => 1) out.source out.history ≤
        248 * (a.runFrom past c keys).1.length + Simulation.Minimum.excess (fun _ => 1) c s :=
  RotationBST.Deamortization.Finger.prepare_excess bounded a past valid budgetBound keys validKeys

theorem transform_excess {α : Type} {sourcePolicy : Simulation.Policy α} {scheduler : Scheduler.Policy}
    (bounded : Simulation.PolicyBounded (fun _ => 1) sourcePolicy) {budget : Nat}
    (schedulerValid : Scheduler.PolicyValid budget scheduler) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ (out : Scheduler.Output) (planned : PreparedOutput α),
      prepare sourcePolicy a past c s keys = some planned ∧
      transform sourcePolicy scheduler a past c s keys = some out ∧
      out.state.planned = ⟨planned.history.pair.tree, []⟩ ∧ Scheduler.Valid budget out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
      Scheduler.ServedStream ⟨s.pair.tree, []⟩ keys out.state.cursor out.instructions out.costs ∧
      Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
        (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.instructions.length + 5 * out.state.pending.length + 5 * Simulation.Minimum.excess (fun _ => 1) planned.source planned.history ≤
        1240 * (a.runFrom past c keys).1.length + 5 * Simulation.Minimum.excess (fun _ => 1) c s ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      ∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget :=
  RotationBST.Deamortization.Finger.transform_excess bounded schedulerValid a past valid budgetBound keys validKeys

theorem minimized_transform {α : Type}
    (c : LabelledCursor.Config α) (live : c.focus ≠ .nil) :
    ∃ (sourcePolicy : Simulation.Policy α) (scheduler : Scheduler.Policy) (budget : Nat)
      (s : State α) (startup : Nat),
      Simulation.PolicyBounded (fun _ => 1) sourcePolicy ∧ Scheduler.PolicyValid budget scheduler ∧
      Simulation.ConfigValid (fun _ => 1) c s ∧
      Simulation.Minimum.excess (fun _ => 1) c s = 0 ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨s.pair.tree, []⟩ startup ∧ startup ≤ 16 * c.tree.erase.size ∧
      (budget : ℝ) < 50 + 39 * Real.logb 2 c.tree.erase.size ∧
      ∀ (a : Simulation.Requests.Algorithm α) (past keys : List Nat), (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, transform sourcePolicy scheduler a past c s keys = some out ∧
          Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
          Scheduler.ServedStream ⟨s.pair.tree, []⟩ keys out.state.cursor out.instructions out.costs ∧
          Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          out.instructions.length ≤ 1240 * (a.runFrom past c keys).1.length ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size :=
  RotationBST.Deamortization.Finger.minimized_transform c live

theorem deamortize {α : Type} (family : List Nat → Simulation.Requests.Algorithm α)
    (c : LabelledCursor.Config α) (live : c.focus ≠ .nil) :
    ∃ (s : State α) (startup : Nat) (program : List Nat → Option Scheduler.Output),
      Simulation.ConfigValid (fun _ => 1) c s ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨s.pair.tree, []⟩ startup ∧ startup ≤ 16 * c.tree.erase.size ∧
      (∀ keys, (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, program keys = some out ∧
          Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
          Scheduler.ServedStream ⟨s.pair.tree, []⟩ keys out.state.cursor out.instructions out.costs ∧
          Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          out.instructions.length ≤ 1240 * ((family keys).runFrom [] c keys).1.length ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size) ∧
      ((∃ a, ∀ keys, family keys = a) →
        ∀ xs ys out, program (xs ++ ys) = some out →
          ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
            first.costs <+: out.costs) :=
  RotationBST.Deamortization.Finger.deamortize family c live

end RotationBST.Deamortization.Finger.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Finger.Results`: 11 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Finger.Results allowing [
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
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Definitions.Abstract]
