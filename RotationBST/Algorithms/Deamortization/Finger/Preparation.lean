module

public import RotationBST.Algorithms.Deamortization.Finger.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Abstract
public import RotationBST.Algorithms.Deamortization.Scheduler.Execution
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

private theorem physical_height {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p)
    {c : LabelledCursor.Config α} {s : State α} (valid : Simulation.ConfigValid (fun _ => 1) c s)
    {ops : List Multifinger.Opcode} {out : Simulation.Output α}
    (completed : Simulation.run p c s ops = some out) {budget : Nat}
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget) :
    Scheduler.Height budget ⟨s.pair.tree, []⟩ out.instructions := by
  intro cut middle first x hx
  obtain ⟨actual, actualReplay, _, depths⟩ :=
    Simulation.Interruption.Results.run_uniform_prefix bounded valid completed cut
  have same : actual = middle := Option.some.inj (actualReplay.symm.trans first)
  subst actual
  have size : s.pair.tree.size = middle.tree.size := by
    obtain ⟨_, _, rotations⟩ := (Multifinger.Replay.Results.physical first).rotations
    exact rotations.size_eq
  have bound := (depths x (by rw [size]; exact hx)).trans budgetBound
  exact_mod_cast bound

theorem initial_valid {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p)
    {c : LabelledCursor.Config α} {s : State α} (valid : Simulation.ConfigValid (fun _ => 1) c s)
    {budget : Nat} (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget) :
    Scheduler.Valid budget (Scheduler.initial ⟨s.pair.tree, []⟩) := by
  have height := physical_height bounded valid (ops := []) (out := ⟨c, s, []⟩) rfl budgetBound
  apply Scheduler.initial_valid (by simp [HeavyPath.Finger.Pair.tree])
  exact height 0 ⟨s.pair.tree, []⟩ rfl

/-- The preparation contract is proved from the actual six-operation source
simulator, including recorded visits, depth bounds, and amortized work. -/
theorem prepare_accounting {α : Type} {p : Simulation.Policy α}
    (bounded : Simulation.PolicyBounded (fun _ => 1) p) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s) {budget : Nat}
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, prepare p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      Simulation.ConfigValid (fun _ => 1) out.source out.history ∧ out.requests.map Scheduler.Request.target = keys ∧
      Scheduler.PreparedStream budget ⟨s.pair.tree, []⟩ out.requests ⟨out.history.pair.tree, []⟩ ∧
      (out.requests.map (fun request => request.instructions.length)).sum + out.history.potential ≤
        62 * (a.runFrom past c keys).1.length + s.potential ∧
      (out.requests.map (fun request => request.instructions.length)).sum +
        Simulation.Minimum.excess (fun _ => 1) out.source out.history ≤
        248 * (a.runFrom past c keys).1.length + Simulation.Minimum.excess (fun _ => 1) c s := by
  induction keys generalizing past c s with
  | nil => exact ⟨⟨c, s, []⟩, rfl, rfl, valid, rfl, .nil, by simp [Simulation.Requests.Algorithm.runFrom]⟩
  | cons key keys ih =>
    have search := a.correct past c key (Simulation.Requests.config_nonempty valid) (validKeys key (by simp))
    obtain ⟨first, firstRun, firstEq, firstValid, firstReplay, firstBound, _, firstVisit⟩ :=
      Simulation.Requests.Results.serves_recorded bounded.1 valid search
    have firstExcess := Simulation.Minimum.Results.run_excess bounded.1 valid search.legal firstRun
    have sourceSize : c.tree.erase.size = first.source.tree.erase.size := by
      rw [firstEq]
      exact Simulation.Requests.source_size search.legal
    have size : s.pair.tree.size = first.state.pair.tree.size := by
      obtain ⟨_, _, rotations⟩ := (Multifinger.Replay.Results.physical firstReplay).rotations
      exact rotations.size_eq
    have nextBudget : 49 + 39 * Real.logb 2 first.state.pair.tree.size ≤ budget := by
      rw [← size]
      exact budgetBound
    have restValid : ∀ x ∈ keys, x < first.source.tree.erase.size := by
      intro x hx
      rw [← sourceSize]
      exact validKeys x (by simp [hx])
    obtain ⟨last, lastRun, lastEq, lastValid, lastKeys, lastReady, lastBound, lastExcess⟩ :=
      ih (past ++ [key]) firstValid nextBudget restValid
    have firstReady : Scheduler.Prepared budget ⟨s.pair.tree, []⟩ ⟨key, first.instructions⟩
        ⟨first.state.pair.tree, []⟩ := ⟨firstReplay, firstVisit, physical_height bounded valid firstRun budgetBound⟩
    refine ⟨⟨last.source, last.history, ⟨key, first.instructions⟩ :: last.requests⟩,
      ?_, ?_, lastValid, ?_, .cons firstReady lastReady, ?_, ?_⟩
    · simp only [prepare, firstRun, Option.bind_some, lastRun, Option.map_some]
    · simpa only [Simulation.Requests.Algorithm.runFrom, firstEq] using lastEq
    · simp only [List.map_cons, lastKeys]
    · rw [firstEq] at lastBound
      simp only [Simulation.Requests.Algorithm.runFrom, Simulation.Output.cost,
        List.map_cons, List.sum_cons, List.length_append] at *
      omega
    · rw [firstEq] at firstExcess lastExcess
      simp only [Simulation.Requests.Algorithm.runFrom, Simulation.Output.cost,
        List.map_cons, List.sum_cons, List.length_append] at *
      omega

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
        62 * (a.runFrom past c keys).1.length + s.potential := by
  obtain ⟨out, completed, source, preserved, targets, ready, work, _⟩ :=
    prepare_accounting bounded a past valid budgetBound keys validKeys
  exact ⟨out, completed, source, preserved, targets, ready, work⟩

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
        248 * (a.runFrom past c keys).1.length + Simulation.Minimum.excess (fun _ => 1) c s := by
  obtain ⟨out, completed, source, preserved, targets, ready, _, work⟩ :=
    prepare_accounting bounded a past valid budgetBound keys validKeys
  exact ⟨out, completed, source, preserved, targets, ready, work⟩

end RotationBST.Deamortization.Finger
