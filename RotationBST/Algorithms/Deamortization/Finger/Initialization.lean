module

public import RotationBST.Algorithms.Deamortization.Finger.Execution
public import Mathlib.Algebra.Order.Floor.Semiring
public import RotationBST.Models.Pointer.Reshape
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

/-- A fixed online transformation with explicit original-tree startup and
logarithmic worst-case request charges. The total comparison retains the
additive initialization allowance instead of hiding it in big-O notation. -/
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
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim (live rfl)
  | node l key r =>
    obtain ⟨s, startup, valid, startupTrace, startupBound, potentialBound, _⟩ :=
      Results.state_initialization_bounded (HeavyPath.Results.unit_positive (LabelledCursor.plug cs (.node l key r)))
    have size : s.pair.tree.size = (LabelledCursor.Config.mk (.node l key r) cs).tree.erase.size :=
      Results.state_size valid
    change startup ≤ 16 * (LabelledCursor.Config.mk (.node l key r) cs).tree.erase.size at startupBound
    change s.potential ≤ 23 * (LabelledCursor.Config.mk (.node l key r) cs).tree.erase.size at potentialBound
    let height : ℝ := 49 + 39 * Real.logb 2 s.pair.tree.size
    let budget := ⌈height⌉₊
    have logarithm : 0 ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_nonneg (by norm_num)
      have population : 1 ≤ s.pair.tree.size := by
        simp only [HeavyPath.Finger.Pair.tree, Tree.size]
        omega
      exact_mod_cast population
    have heightNonnegative : 0 ≤ height := by dsimp [height]; linarith
    have budgetBound : height ≤ budget := Nat.le_ceil height
    have budgetUpper : (budget : ℝ) < 50 + 39 * Real.logb 2 s.pair.tree.size := by
      have rounded := Nat.ceil_lt_add_one heightNonnegative
      dsimp [height] at rounded
      exact rounded.trans_le (by ring_nf; rfl)
    obtain ⟨sourcePolicy, bounded⟩ := Simulation.Results.policy_bounded_exists (fun _ : α => (1 : ℝ))
    obtain ⟨scheduler, schedulerValid⟩ := Scheduler.policy_exists budget
    refine ⟨sourcePolicy, scheduler, budget, s, startup, bounded, schedulerValid,
      valid, startupTrace, startupBound, ?_, ?_⟩
    · simpa only [size] using budgetUpper
    · intro past keys validKeys
      obtain ⟨out, planned, _, completed, _, _, replay, execution, work, count, total, costs⟩ :=
        transform_spec bounded schedulerValid a past (c := ⟨.node l key r, cs⟩) valid budgetBound keys validKeys
      refine ⟨out, completed, replay, execution, ?_, count, total, ?_⟩
      · omega
      · intro cost member
        have costNat := costs cost member
        have costReal : (cost : ℝ) ≤ 1 + 5 * (budget : ℝ) := by exact_mod_cast costNat
        rw [size] at budgetUpper
        linarith

/-- Choose the initial representation and both causal policies before every
source algorithm and request stream. Minimum-relative initial credit is zero,
so physical execution has a purely multiplicative source-operation bound.
The optional original-tree reshaping cost is returned separately. -/
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
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim (live rfl)
  | node l key r =>
    obtain ⟨canonical, _, canonicalValid, _, _, _, _⟩ :=
      Results.state_initialization_bounded (HeavyPath.Results.unit_positive (LabelledCursor.plug cs (.node l key r)))
    obtain ⟨s, valid, minimum⟩ := Simulation.Minimum.Results.attained
      (c := ⟨.node l key r, cs⟩) canonicalValid
    have zero : Simulation.Minimum.excess (fun _ => 1) ⟨.node l key r, cs⟩ s = 0 := by
      simp only [Simulation.Minimum.excess, minimum, Nat.sub_self]
    have size : s.pair.tree.size = (LabelledCursor.Config.mk (.node l key r) cs).tree.erase.size :=
      Results.state_size valid
    obtain ⟨startup, startupBound, startupTrace⟩ := Pointer.reshape
      (LabelledCursor.Config.mk (.node l key r) cs).tree.erase s.pair.tree size.symm
    let height : ℝ := 49 + 39 * Real.logb 2 s.pair.tree.size
    let budget := ⌈height⌉₊
    have logarithm : 0 ≤ Real.logb 2 s.pair.tree.size := by
      apply Real.logb_nonneg (by norm_num)
      have population : 1 ≤ s.pair.tree.size := by
        simp only [HeavyPath.Finger.Pair.tree, Tree.size]
        omega
      exact_mod_cast population
    have heightNonnegative : 0 ≤ height := by dsimp [height]; linarith
    have budgetBound : height ≤ budget := Nat.le_ceil height
    have budgetUpper : (budget : ℝ) < 50 + 39 * Real.logb 2 s.pair.tree.size := by
      have rounded := Nat.ceil_lt_add_one heightNonnegative
      dsimp [height] at rounded
      exact rounded.trans_le (by ring_nf; rfl)
    obtain ⟨sourcePolicy, bounded⟩ := Simulation.Results.policy_bounded_exists (fun _ : α => (1 : ℝ))
    obtain ⟨scheduler, schedulerValid⟩ := Scheduler.policy_exists budget
    refine ⟨sourcePolicy, scheduler, budget, s, startup, bounded, schedulerValid,
      valid, zero, startupTrace, startupBound, ?_, ?_⟩
    · simpa only [size] using budgetUpper
    · intro a past keys validKeys
      obtain ⟨out, planned, _, completed, _, _, replay, served, execution, work, count, total, costs⟩ :=
        transform_excess bounded schedulerValid a past (c := ⟨.node l key r, cs⟩) valid budgetBound keys validKeys
      refine ⟨out, completed, replay, served, execution, ?_, count, total, ?_⟩
      · rw [zero] at work
        omega
      · intro cost member
        have costNat := costs cost member
        have costReal : (cost : ℝ) ≤ 1 + 5 * (budget : ℝ) := by exact_mod_cast costNat
        rw [size] at budgetUpper
        linarith

end RotationBST.Deamortization.Finger
