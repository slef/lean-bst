module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Worker.Replay.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Worker.Replay.Results
open Multifinger

variable {σ : Type} {saved : Tree} (planner : Planner σ saved)

theorem access (side : Bool) (state : σ) (x : Nat)
    (size : (planner.tree side state).size = saved.size) (valid : x < saved.size) :
    Worker.Access (worker planner) side (.boundary state) x (.boundary (planner.plan side state x).1)
      ((planner.plan side state x).2.length + 2) :=
  RotationBST.Combo.Worker.Replay.access planner side state x size valid

theorem requests (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    Worker.Requests (worker planner) side (.boundary state) xs (.boundary (run planner side state xs).1)
      (run planner side state xs).2 :=
  RotationBST.Combo.Worker.Replay.requests planner side state xs size valid

theorem request_boundary {side : Bool} {state : State σ}
    (boundary : Refinement.Visits.Boundary (worker planner) saved.size side state) :
    ∃ original, state = .boundary original ∧ (planner.tree side original).size = saved.size :=
  RotationBST.Combo.Worker.Replay.request_boundary planner boundary

theorem correct : Refinement.Visits.Correct (model planner) :=
  RotationBST.Combo.Worker.Replay.correct planner

theorem rooted {s t : Tree} {x cost : Nat} (served : Pointer.Serves s t x cost) :
    ∃ ops, replay ops ⟨s, []⟩ = some ⟨t, []⟩ ∧ Visits x ops ⟨s, []⟩ ∧ ops.length + 2 ≤ 2 * cost :=
  RotationBST.Combo.Worker.Replay.rooted served

theorem planner_exists {σ : Type} {saved : Tree}
    (initial : Bool → σ) (tree : Bool → σ → Tree) (next : Bool → σ → Nat → σ × Nat)
    (initialTree : ∀ side, tree side (initial side) = saved)
    (correct : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
      Pointer.Serves (tree side state) (tree side (next side state x).1) x (next side state x).2) :
    ∃ planner : Planner σ saved, planner.initial = initial ∧ planner.tree = tree ∧
      ∀ side state x, (tree side state).size = saved.size → x < saved.size →
        (planner.plan side state x).1 = (next side state x).1 ∧
        (planner.plan side state x).2.length + 2 ≤ 2 * (next side state x).2 :=
  RotationBST.Combo.Worker.Replay.planner_exists initial tree next initialTree correct

theorem run_bound {σ : Type} {saved : Tree} (planner : Planner σ saved)
    (next : Bool → σ → Nat → σ × Nat)
    (expansion : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (planner.plan side state x).1 = (next side state x).1 ∧
      (planner.plan side state x).2.length + 2 ≤ 2 * (next side state x).2)
    (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    (run planner side state xs).1 = (policyRun next side state xs).1 ∧
      (run planner side state xs).2 ≤ 2 * (policyRun next side state xs).2 :=
  RotationBST.Combo.Worker.Replay.run_bound planner next expansion side state xs size valid

theorem short_rooted (s t : Tree) (x : Nat) (same : s.size = t.size) (valid : x < s.size) :
    ∃ ops, replay ops ⟨s, []⟩ = some ⟨t, []⟩ ∧ Visits x ops ⟨s, []⟩ ∧ ops.length + 2 ≤ 20 * s.size :=
  RotationBST.Combo.Worker.Replay.short_rooted s t x same valid

theorem bounded_planner {σ : Type} {saved : Tree} (planner : Planner σ saved) :
    ∃ bounded : Planner σ saved,
      bounded.initial = planner.initial ∧ bounded.tree = planner.tree ∧
      (∀ side state x, (bounded.plan side state x).1 = (planner.plan side state x).1) ∧
      ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
        (bounded.plan side state x).2.length ≤ (planner.plan side state x).2.length ∧
        (bounded.plan side state x).2.length + 2 ≤ 20 * saved.size :=
  RotationBST.Combo.Worker.Replay.bounded_planner planner

theorem refined_run {σ : Type} {saved : Tree} (planner bounded : Planner σ saved)
    (sameNext : ∀ side state x, (bounded.plan side state x).1 = (planner.plan side state x).1)
    (shorter : ∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
      (bounded.plan side state x).2.length ≤ (planner.plan side state x).2.length)
    (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    (run bounded side state xs).1 = (run planner side state xs).1 ∧
      (run bounded side state xs).2 ≤ (run planner side state xs).2 :=
  RotationBST.Combo.Worker.Replay.refined_run planner bounded sameNext shorter side state xs size valid

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
    Analysis.WellBehaved (worker bounded) saved.size overhead C₀ C₁ charges :=
  RotationBST.Combo.Worker.Replay.bounded_well_behaved planner bounded sameInitial sameTree sameNext shorter single overhead C₀ C₁ charges size constant nonneg upper stable

theorem algorithm_planner (a : Bool → RotationBST.Algorithm) (saved : Tree) :
    ∃ planner : Planner (List Nat × Pointer.Lazy.Online.State) saved,
      (∀ side state x, (planner.tree side state).size = saved.size → x < saved.size →
        (planner.plan side state x).2.length + 2 ≤ 20 * saved.size) ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        (run planner side (planner.initial side) xs).2 ≤ 64 * (a side).totalCost saved xs :=
  RotationBST.Combo.Worker.Replay.algorithm_planner a saved

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
        Analysis.WellBehaved (worker planner) saved.size overhead C₀ C₁ charges :=
  RotationBST.Combo.Worker.Replay.algorithms_well_behaved a saved

end RotationBST.Combo.Worker.Replay.Results

/-- info: abstract audit passed for `RotationBST.Combo.Worker.Replay.Results`: 13 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Worker.Replay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract]
