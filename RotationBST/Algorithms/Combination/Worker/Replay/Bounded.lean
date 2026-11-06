module

public import RotationBST.Algorithms.Combination.Worker.Replay.Policy
public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract
public import RotationBST.Models.Pointer.Reshape
public import RotationBST.Bounds.StaticTree.Comparison
public import RotationBST.Bounds.LazyFinger.Initialization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

/-- A short root-to-root request can visit its key and retain any prescribed
final tree of the same size. Initialization is charged within the log. -/
theorem short_rooted (s t : Tree) (x : Nat) (same : s.size = t.size) (valid : x < s.size) :
    ∃ ops, replay ops ⟨s, []⟩ = some ⟨t, []⟩ ∧ Visits x ops ⟨s, []⟩ ∧ ops.length + 2 ≤ 20 * s.size := by
  obtain ⟨search, searched, visited, searchBound⟩ := rooted (StaticTree.serves s x valid)
  obtain ⟨k, bound, trace⟩ := Pointer.reshape s t same
  obtain ⟨change, length, changed⟩ := Multifinger.Replay.Results.record trace
  have depth := LazyFinger.depth_le_size s x
  refine ⟨search ++ change, ?_, ?_, ?_⟩
  · rw [replay_append, searched, Option.bind_some, changed]
  · obtain ⟨before, after, current, split, reached, key⟩ := visited
    exact ⟨before, after ++ change, current, by rw [split, List.append_assoc], reached, key⟩
  · simp only [List.length_append, length]
    omega

/-- Choose one causal planner before any comparator or request sequence.
Successor states are identical, logs never get longer, and every valid access
has linear cost. Classical planning time is outside the abstract BST model. -/
theorem bounded_planner {σ : Type} {saved : Tree} (planner : Planner σ saved) :
    ∃ bounded : Planner σ saved,
      bounded.initial = planner.initial ∧ bounded.tree = planner.tree ∧
      (∀ side state x, (bounded.plan side state x).1 = (planner.plan side state x).1) ∧
      ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
        (bounded.plan side state x).2.length ≤ (planner.plan side state x).2.length ∧
        (bounded.plan side state x).2.length + 2 ≤ 20 * saved.size := by
  classical
  have available : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      ∃ ops, replay ops ⟨planner.tree side state, []⟩ = some ⟨planner.tree side (planner.plan side state x).1, []⟩ ∧
        Visits x ops ⟨planner.tree side state, []⟩ ∧
        ops.length ≤ (planner.plan side state x).2.length ∧ ops.length + 2 ≤ 20 * saved.size := by
    intro side state x size valid
    by_cases short : (planner.plan side state x).2.length + 2 ≤ 20 * saved.size
    · exact ⟨_, planner.legal side state x size valid, planner.visits side state x size valid, le_rfl, short⟩
    · obtain ⟨ops, legal, visits, bound⟩ := short_rooted (planner.tree side state)
        (planner.tree side (planner.plan side state x).1) x
        (size.trans (plan_size planner side state x size valid).symm) (by omega)
      rw [size] at bound
      exact ⟨ops, legal, visits, by omega, bound⟩
  let log := fun side state x =>
    if valid : (planner.tree side state).size = saved.size ∧ x < saved.size then
      Classical.choose (available side state x valid.1 valid.2)
    else []
  have spec : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      replay (log side state x) ⟨planner.tree side state, []⟩ = some ⟨planner.tree side (planner.plan side state x).1, []⟩ ∧
      Visits x (log side state x) ⟨planner.tree side state, []⟩ ∧
      (log side state x).length ≤ (planner.plan side state x).2.length ∧
      (log side state x).length + 2 ≤ 20 * saved.size := by
    intro side state x size valid
    dsimp only [log]
    rw [dite_eq_left ⟨size, valid⟩]
    exact Classical.choose_spec (available side state x size valid)
  let bounded : Planner σ saved :=
    ⟨planner.initial, planner.tree, fun side state x => ((planner.plan side state x).1, log side state x),
      planner.initial_tree, fun side state x size valid => (spec side state x size valid).1,
      fun side state x size valid => (spec side state x size valid).2.1⟩
  exact ⟨bounded, rfl, rfl, fun _ _ _ => rfl, fun side state x size valid => (spec side state x size valid).2.2⟩

/-- State-preserving shortening retains every prefix/sequence cost bound. -/
theorem refined_run {σ : Type} {saved : Tree} (planner bounded : Planner σ saved)
    (sameNext : ∀ side state x, (bounded.plan side state x).1 = (planner.plan side state x).1)
    (shorter : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (bounded.plan side state x).2.length ≤ (planner.plan side state x).2.length)
    (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    (run bounded side state xs).1 = (run planner side state xs).1 ∧
      (run bounded side state xs).2 ≤ (run planner side state xs).2 := by
  induction xs generalizing state with
  | nil => exact ⟨rfl, le_rfl⟩
  | cons x xs ih =>
      have key := valid x (by simp)
      have bound := shorter side state x size key
      have tail := ih (planner.plan side state x).1 (plan_size planner side state x size key)
        (by intro y member; exact valid y (by simp [member]))
      simp only [run, sameNext]
      exact ⟨tail.1, by omega⟩

/-- The capped planner supplies the missing per-access hypothesis. Upper
and segment bounds are inherited uniformly for every comparator. -/
theorem bounded_well_behaved {σ : Type} {saved : Tree} (planner bounded : Planner σ saved)
    (sameInitial : bounded.initial = planner.initial) (sameTree : bounded.tree = planner.tree)
    (sameNext : ∀ side state x, (bounded.plan side state x).1 = (planner.plan side state x).1)
    (shorter : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (bounded.plan side state x).2.length ≤ (planner.plan side state x).2.length)
    (single : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (bounded.plan side state x).2.length + 2 ≤ 20 * saved.size)
    (overhead C₀ C₁ : Nat) (charges : Analysis.Charges) (size : saved.size ≤ overhead) (constant : 20 ≤ C₁)
    (nonneg : ∀ side xs i, 0 ≤ charges side xs i)
    (upper : ∀ side xs, (∀ x ∈ xs, x < saved.size) →
      ((run planner side (planner.initial side) xs).2 : ℝ) ≤ Analysis.total charges side xs + overhead)
    (stable : ∀ side xs, (∀ x ∈ xs, x < saved.size) → ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
      Analysis.total charges side (Analysis.segment xs lo hi) + overhead ≤
        C₀ * Analysis.mass charges side xs lo hi + C₁ * overhead) :
    Analysis.WellBehaved (worker bounded) saved.size overhead C₀ C₁ charges := by
  refine ⟨nonneg, ?_, ?_, stable⟩
  · intro side earlier state spent ran valid x key
    obtain ⟨original, rfl, treeSize⟩ := request_boundary bounded ⟨earlier, spent, ran, valid⟩
    have bound := single side original x (by simpa only [sameTree] using treeSize) key
    exact ⟨_, _, access bounded side original x treeSize key,
      bound.trans (Nat.mul_le_mul constant size)⟩
  · intro side xs valid
    have initialSize := congrArg Tree.size (planner.initial_tree side)
    have shortened := (refined_run planner bounded sameNext shorter side (planner.initial side) xs initialSize valid).2
    have charged := upper side xs valid
    refine ⟨_, _, requests bounded side (bounded.initial side) xs
      (congrArg Tree.size (bounded.initial_tree side)) valid, ?_⟩
    rw [sameInitial]
    exact (Nat.cast_le.mpr shortened).trans charged

end RotationBST.Combo.Worker.Replay
