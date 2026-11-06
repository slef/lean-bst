module

public import RotationBST.Algorithms.Combination.Worker.Replay.Bounded
public import RotationBST.Models.Pointer.Lazy.Online.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay

private noncomputable def pointerNext (a : Bool → RotationBST.Algorithm) (side : Bool)
    (state : List Nat × Pointer.Lazy.Online.State) (x : Nat) :
    (List Nat × Pointer.Lazy.Online.State) × Nat :=
  let next := Pointer.Lazy.Online.advance (a side) state.1 state.2 x
  ((state.1 ++ [x], next.1), next.2)

private theorem pointerRun (a : Bool → RotationBST.Algorithm) (side : Bool)
    (past : List Nat) (state : Pointer.Lazy.Online.State) (xs : List Nat) :
    policyRun (pointerNext a) side (past, state) xs =
      ((past ++ xs, (Pointer.Lazy.Online.run (a side) past state xs).1),
        (Pointer.Lazy.Online.run (a side) past state xs).2) := by
  induction xs generalizing past state with
  | nil => simp [policyRun, Pointer.Lazy.Online.run]
  | cons x xs ih =>
      simp only [policyRun, pointerNext, Pointer.Lazy.Online.run, ih]
      simp [List.append_assoc]

/-- Any certified rotation-model algorithm supplies one causal, linearly
bounded replay worker. It preserves all aggregate bounds up to a universal
factor; its construction does not depend on weights or other comparators.
The source history and classical planning remain allowed abstract BST state. -/
theorem algorithm_planner (a : Bool → RotationBST.Algorithm) (saved : Tree) :
    ∃ planner : Planner (List Nat × Pointer.Lazy.Online.State) saved,
      (∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
        (planner.plan side state x).2.length + 2 ≤ 20 * saved.size) ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        (run planner side (planner.initial side) xs).2 ≤ 64 * (a side).totalCost saved xs := by
  let start : Bool → List Nat × Pointer.Lazy.Online.State := fun _ => ([], Pointer.Lazy.Online.initial saved)
  let tree : Bool → (List Nat × Pointer.Lazy.Online.State) → Tree := fun _ state => state.2.current
  have legal : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
      Pointer.Serves (tree side state) (tree side (pointerNext a side state x).1) x (pointerNext a side state x).2 := by
    intro side state x size valid
    have same := state.2.certificate.size_eq
    have key : x < state.2.virtual.size := by dsimp only [tree] at size; omega
    exact (Pointer.Lazy.Online.advance_spec (a side) state.1 state.2 x key).1
  obtain ⟨source, initial, trees, expansion⟩ := planner_exists start tree (pointerNext a) (fun _ => rfl) legal
  obtain ⟨bounded, sameInitial, sameTree, sameNext, shortened⟩ := bounded_planner source
  refine ⟨bounded, ?_, ?_⟩
  · intro side state x size valid
    exact (shortened side state x (by simpa only [sameTree] using size) valid).2
  · intro side xs valid
    have first := (refined_run source bounded sameNext
      (fun side state x size valid => (shortened side state x size valid).1)
      side (source.initial side) xs (congrArg Tree.size (source.initial_tree side)) valid).2
    have second := (run_bound source (pointerNext a)
      (by simpa only [trees] using expansion) side (source.initial side) xs
      (congrArg Tree.size (source.initial_tree side)) valid).2
    rw [initial] at second
    simp only [start, pointerRun] at second
    have third := (Pointer.Lazy.Online.Results.simulation (a side) [] saved xs valid).2.2
    rw [sameInitial]
    rw [initial] at first ⊢
    simp only [start] at first ⊢
    unfold RotationBST.Algorithm.totalCost RotationBST.Algorithm.cost
    omega

/-- One pair of source algorithms yields a fixed pair of interruptible workers
before any comparator is supplied. Nonnegative segment-stable aggregate bounds
then satisfy the operational combination contract. -/
theorem algorithms_well_behaved (a : Bool → RotationBST.Algorithm) (saved : Tree) :
    ∃ planner : Planner (List Nat × Pointer.Lazy.Online.State) saved,
      ∀ (overhead C₀ C₁ : Nat) (charges : Analysis.Charges),
        saved.size ≤ overhead → 20 ≤ C₁ →
        (∀ side xs i, 0 ≤ charges side xs i) →
        (∀ side xs, (∀ x ∈ xs, x < saved.size) →
          (64 : ℝ) * (a side).totalCost saved xs ≤ Analysis.total charges side xs + overhead) →
        (∀ side xs, (∀ x ∈ xs, x < saved.size) → ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
          Analysis.total charges side (Analysis.segment xs lo hi) + overhead ≤
            C₀ * Analysis.mass charges side xs lo hi + C₁ * overhead) →
        Analysis.WellBehaved (worker planner) saved.size overhead C₀ C₁ charges := by
  obtain ⟨planner, single, upper⟩ := algorithm_planner a saved
  refine ⟨planner, ?_⟩
  intro overhead C₀ C₁ charges size constant nonneg charged stable
  apply bounded_well_behaved planner planner rfl rfl (fun _ _ _ => rfl)
    (fun _ _ _ _ _ => le_rfl) single overhead C₀ C₁ charges size constant nonneg _ stable
  intro side xs valid
  have bound : ((run planner side (planner.initial side) xs).2 : ℝ) ≤
      64 * (a side).totalCost saved xs := by exact_mod_cast upper side xs valid
  exact bound.trans (charged side xs valid)

end RotationBST.Combo.Worker.Replay
