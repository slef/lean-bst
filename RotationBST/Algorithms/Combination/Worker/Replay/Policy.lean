module

public import RotationBST.Algorithms.Combination.Worker.Replay.Rooted
public import RotationBST.Algorithms.Combination.Worker.Replay.Execution

@[expose] public section
namespace RotationBST.Combo.Worker.Replay

/-- Choose logs from a causal pointer policy once, before any request sequence
is presented. Each log includes the charged return to the root. -/
theorem planner_exists {σ : Type} {saved : Tree}
    (initial : Bool → σ) (tree : Bool → σ → Tree) (next : Bool → σ → Nat → σ × Nat)
    (initialTree : ∀ side, tree side (initial side) = saved)
    (correct : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
      Pointer.Serves (tree side state) (tree side (next side state x).1) x (next side state x).2) :
    ∃ planner : Planner σ saved, planner.initial = initial ∧ planner.tree = tree ∧
      ∀ side state x, (tree side state).size = saved.size → x < saved.size →
        (planner.plan side state x).1 = (next side state x).1 ∧
        (planner.plan side state x).2.length + 2 ≤ 2 * (next side state x).2 := by
  classical
  let log := fun side state x =>
    if valid : (tree side state).size = saved.size ∧ x < saved.size then
      Classical.choose (rooted (correct side state x valid.1 valid.2))
    else []
  have spec : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
      Multifinger.replay (log side state x) ⟨tree side state, []⟩ = some ⟨tree side (next side state x).1, []⟩ ∧
      Visits x (log side state x) ⟨tree side state, []⟩ ∧
      (log side state x).length + 2 ≤ 2 * (next side state x).2 := by
    intro side state x size valid
    dsimp only [log]
    rw [dite_eq_left (And.intro size valid)]
    exact Classical.choose_spec (rooted (correct side state x size valid))
  let planner : Planner σ saved :=
    ⟨initial, tree, fun side state x => ((next side state x).1, log side state x), initialTree,
      fun side state x size valid => (spec side state x size valid).1,
      fun side state x size valid => (spec side state x size valid).2.1⟩
  exact ⟨planner, rfl, rfl, fun side state x size valid => ⟨rfl, (spec side state x size valid).2.2⟩⟩

/-- Pointwise trace expansion composes through the actual successor states.
The same planner serves every prefix with at most twice the source-policy cost. -/
theorem run_bound {σ : Type} {saved : Tree} (planner : Planner σ saved)
    (next : Bool → σ → Nat → σ × Nat)
    (expansion : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (planner.plan side state x).1 = (next side state x).1 ∧
      (planner.plan side state x).2.length + 2 ≤ 2 * (next side state x).2)
    (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    (run planner side state xs).1 = (policyRun next side state xs).1 ∧
      (run planner side state xs).2 ≤ 2 * (policyRun next side state xs).2 := by
  induction xs generalizing state with
  | nil => exact ⟨rfl, by simp [run, policyRun]⟩
  | cons x xs ih =>
    have key := valid x (by simp)
    obtain ⟨same, bound⟩ := expansion side state x size key
    have tail := ih (planner.plan side state x).1 (plan_size planner side state x size key)
      (by intro y member; exact valid y (by simp [member]))
    simp only [run, policyRun]
    rw [← same]
    exact ⟨tail.1, by omega⟩

end RotationBST.Combo.Worker.Replay
