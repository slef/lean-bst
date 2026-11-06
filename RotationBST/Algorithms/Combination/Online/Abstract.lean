module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Online.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Online.Results

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}

theorem completes (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : (Controller.serve worker budget restore s.controller x).done = true :=
  RotationBST.Combo.Online.completes contract s x valid

theorem advance_spec (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : Transition restore s x (advance contract s x) :=
  RotationBST.Combo.Online.advance_spec contract s x valid

theorem run_append (contract : Contract model data budget restore) (s : State model data budget) (xs ys : List Nat) :
    run contract s (xs ++ ys) =
      let first := run contract s xs
      let rest := run contract first.1 ys
      (rest.1, first.2 + rest.2) :=
  RotationBST.Combo.Online.run_append contract s xs ys

theorem run_spec (contract : Contract model data budget restore) (s : State model data budget)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ work switches,
      Controller.Execution worker budget restore s.controller xs (run contract s xs).1.controller work switches ∧
      Pointer.Execution s.hand.tree xs (run contract s xs).1.hand.tree (run contract s xs).2 ∧
      (run contract s xs).2 + (run contract s xs).1.hand.potential ≤ 8384 * work + s.hand.potential :=
  RotationBST.Combo.Online.run_spec contract s xs valid

theorem execute_append (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) (xs ys : List Nat) :
    execute p s (xs ++ ys) =
      let first := execute p s xs
      let rest := execute p first.1 ys
      (rest.1, first.2 + rest.2) :=
  RotationBST.Combo.Online.execute_append p s xs ys

theorem execute_ready (p : Prepared model budget restore fields oldData)
    (s : State model p.data budget) (xs : List Nat) :
    execute p (some s) xs = (some (run p.contract s xs).1, (run p.contract s xs).2) :=
  RotationBST.Combo.Online.execute_ready p s xs

theorem execute_first (p : Prepared model budget restore fields oldData) (x : Nat) (xs : List Nat) :
    execute p none (x :: xs) =
      (some (run p.contract p.state (x :: xs)).1, p.cost + (run p.contract p.state (x :: xs)).2) :=
  RotationBST.Combo.Online.execute_first p x xs

theorem execute_spec (p : Prepared model budget restore fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final work switches,
      Controller.Execution worker budget restore (Controller.initial worker budget) xs final work switches ∧
      Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
      (execute p none xs).2 ≤ 524 * p.saveCost + 8384 * work :=
  RotationBST.Combo.Online.execute_spec p xs valid

theorem minimum_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
      ((execute p none xs).2 : ℝ) ≤ 524 * (1088 * saved.size : ℝ) +
        8384 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Online.minimum_bound well p xs valid

theorem prefix_policy (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∀ xs, (∀ x ∈ xs, x < saved.size) →
        Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
          ((execute p none xs).2 : ℝ) ≤ 524 * (1088 * saved.size : ℝ) + 8384 * (C₁ + 1 + 57 : Nat) *
            (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Online.prefix_policy model correct well nonempty size fields oldData

theorem stored_potential (s : State model data budget) : s.hand.potential ≤ 32 * saved.size :=
  RotationBST.Combo.Online.State.potential s

theorem remaining_budget (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) : (p.controller s).left ≤ budget :=
  RotationBST.Combo.Online.Prepared.left_le p s

theorem execute_from (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final work switches,
      Controller.Execution worker budget restore (p.controller s) xs final work switches ∧
      Pointer.Execution (p.current s) xs (p.current (execute p s xs).1) (execute p s xs).2 ∧
      (execute p s xs).2 ≤ 570112 * saved.size + 8384 * work :=
  RotationBST.Combo.Online.execute_from p s xs valid

theorem window_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (s : Option (State model p.data (Analysis.budget overhead C₁)))
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    Pointer.Execution (p.current s) (Analysis.segment xs lo hi)
        (p.current (execute p s (Analysis.segment xs lo hi)).1) (execute p s (Analysis.segment xs lo hi)).2 ∧
      ((execute p s (Analysis.segment xs lo hi)).2 : ℝ) ≤ 570112 * (saved.size : ℝ) +
        8384 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
            (2 * C₀ * C₁ + 5) * overhead) :=
  RotationBST.Combo.Online.window_bound well p s xs valid lo hi ordered inside

theorem execute_window_split (p : Prepared model budget restore fields oldData)
    (xs : List Nat) (lo hi : Nat) (ordered : lo ≤ hi) :
    let first := execute p none (xs.take lo)
    let middle := execute p first.1 (Analysis.segment xs lo hi)
    let last := execute p middle.1 (xs.drop hi)
    execute p none xs = (last.1, first.2 + middle.2 + last.2) :=
  RotationBST.Combo.Online.execute_window_split p xs lo hi ordered

theorem executed_window {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := execute p none (xs.take lo)
    let middle := execute p first.1 (Analysis.segment xs lo hi)
    let last := execute p middle.1 (xs.drop hi)
    execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      (middle.2 : ℝ) ≤ 570112 * (saved.size : ℝ) + 8384 * (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
          (2 * C₀ * C₁ + 5) * overhead) :=
  RotationBST.Combo.Online.executed_window well p xs valid lo hi ordered inside

theorem window_policy (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∀ xs, (∀ x ∈ xs, x < saved.size) →
        Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
        ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
          let first := execute p none (xs.take lo)
          let middle := execute p first.1 (Analysis.segment xs lo hi)
          let last := execute p middle.1 (xs.drop hi)
          execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
            Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
            (middle.2 : ℝ) ≤ 8384 * (C₁ + 1 + 57 : Nat) *
              (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
                (2 * C₀ * C₁ + 73) * overhead) :=
  RotationBST.Combo.Online.window_policy model correct well nonempty size fields oldData

end RotationBST.Combo.Online.Results

/-- info: abstract audit passed for `RotationBST.Combo.Online.Results`: 17 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Online.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Startup.Definitions.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Pointer.Routing.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Access.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Maintenance.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Requests.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Erasure.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.BSTDeque.Definitions.Abstract,
  RotationBST.Structures.BSTDeque.Boundary.Definitions.Abstract,
  RotationBST.Structures.Tendon.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Packed.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Startup.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Algorithm.Abstract]
