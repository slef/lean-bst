module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Family.Physical.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Family.Physical.Results

theorem executed_window {ι : Type} [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := Online.execute p none (xs.take lo)
    let middle := Online.execute p first.1 (Analysis.segment xs lo hi)
    let last := Online.execute p middle.1 (xs.drop hi)
    Online.execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      ∀ i, (middle.2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * mass (charges i) xs lo hi +
        (overheadFactor C₀ C₁ * overhead : Nat) :=
  RotationBST.Combo.Family.Physical.executed_window algorithm guaranteed p size xs valid lo hi ordered inside

theorem window_minimum {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := Online.execute p none (xs.take lo)
    let middle := Online.execute p first.1 (Analysis.segment xs lo hi)
    let last := Online.execute p middle.1 (xs.drop hi)
    Online.execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      (middle.2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * minimumMass charges xs lo hi +
        (overheadFactor C₀ C₁ * overhead : Nat) :=
  RotationBST.Combo.Family.Physical.window_minimum algorithm guaranteed p size xs valid lo hi ordered inside

theorem prefix_minimum {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.current (Online.execute p none xs).1) (Online.execute p none xs).2 ∧
      ((Online.execute p none xs).2 : ℝ) ≤ (chargeFactor C₀ C₁ factor : ℝ) * Family.minimum charges xs +
        (overheadFactor C₀ C₁ * overhead : Nat) :=
  RotationBST.Combo.Family.Physical.prefix_minimum algorithm guaranteed p size xs valid

theorem bounded {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData)
    (size : saved.size ≤ overhead) :
    Bounded p (chargeFactor C₀ C₁ factor) (overheadFactor C₀ C₁ * overhead) charges :=
  RotationBST.Combo.Family.Physical.bounded algorithm guaranteed p size

theorem policy_exists {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Online.Prepared algorithm.model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      Bounded p (chargeFactor C₀ C₁ factor) (overheadFactor C₀ C₁ * overhead) charges :=
  RotationBST.Combo.Family.Physical.policy_exists algorithm guaranteed nonempty size fields oldData

theorem combine {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∃ p : Online.Prepared output.model (Analysis.budget (overheadScale C₀ C₁ depth * overhead) (C₁ + depth))
          (57 * (overheadScale C₀ C₁ depth * overhead)) fields oldData,
        Bounded p (chargeFactor C₀ (C₁ + depth) (chargeScale C₀ C₁ depth))
          (overheadFactor C₀ (C₁ + depth) * (overheadScale C₀ C₁ depth * overhead)) charges :=
  RotationBST.Combo.Family.Physical.combine depth overhead C₀ C₁ capacity inputs charges well nonempty size fields oldData

theorem finite_policy {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    let depth := Nat.clog 2 (Fintype.card ι)
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∃ p : Online.Prepared output.model (Analysis.budget (overheadScale C₀ C₁ depth * overhead) (C₁ + depth))
          (57 * (overheadScale C₀ C₁ depth * overhead)) fields oldData,
        Bounded p (chargeFactor C₀ (C₁ + depth) (chargeScale C₀ C₁ depth))
          (overheadFactor C₀ (C₁ + depth) * (overheadScale C₀ C₁ depth * overhead)) charges :=
  RotationBST.Combo.Family.Physical.finite_policy overhead C₀ C₁ inputs charges well nonempty size fields oldData

end RotationBST.Combo.Family.Physical.Results

/-- info: abstract audit passed for `RotationBST.Combo.Family.Physical.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Family.Physical.Results allowing [
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
  RotationBST.Algorithms.Combination.Online.Algorithm.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract,
  RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Family.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Family.Physical.Definitions.Abstract]
