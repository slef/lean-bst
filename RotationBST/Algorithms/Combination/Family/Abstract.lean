module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Family.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Family.Results

theorem overheadScale_pos (C₀ C₁ depth : Nat) : 0 < overheadScale C₀ C₁ depth :=
  RotationBST.Combo.Family.overheadScale_pos C₀ C₁ depth

theorem balanced {saved : Tree} (depth overhead C₀ C₁ : Nat)
    (inputs : Index depth → Algorithm saved) (charges : Index depth → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges :=
  RotationBST.Combo.Family.balanced depth overhead C₀ C₁ inputs charges well nonempty size fields oldData

theorem finite {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges :=
  RotationBST.Combo.Family.finite depth overhead C₀ C₁ capacity inputs charges well nonempty size fields oldData

theorem exists_combination {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead) C₀ (C₁ + Nat.clog 2 (Fintype.card ι))
        (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι))) charges :=
  RotationBST.Combo.Family.exists_combination overhead C₀ C₁ inputs charges well nonempty size fields oldData

theorem requests {ι : Type} [Nonempty ι] {saved : Tree} (algorithm : Algorithm saved)
    {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final cost, Worker.Requests algorithm.worker side (algorithm.worker.restart side) xs final cost ∧
      ∀ i, (cost : ℝ) ≤ (factor : ℝ) * total (charges i) xs + overhead :=
  RotationBST.Combo.Family.requests algorithm guaranteed side xs valid

theorem minimum_bound {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (algorithm : Algorithm saved) {overhead C₀ C₁ factor : Nat} {charges : ι → Charge}
    (guaranteed : Guarantees algorithm overhead C₀ C₁ factor charges)
    (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final cost, Worker.Requests algorithm.worker side (algorithm.worker.restart side) xs final cost ∧
      (cost : ℝ) ≤ (factor : ℝ) * minimum charges xs + overhead :=
  RotationBST.Combo.Family.minimum_bound algorithm guaranteed side xs valid

theorem combine {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (depth overhead C₀ C₁ : Nat) (capacity : Fintype.card ι ≤ 2 ^ depth)
    (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ depth * overhead) C₀ (C₁ + depth)
        (chargeScale C₀ C₁ depth) charges ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        ∃ final cost, Worker.Requests output.worker side (output.worker.restart side) xs final cost ∧
          ∀ i, (cost : ℝ) ≤ (chargeScale C₀ C₁ depth : ℝ) * total (charges i) xs +
            (overheadScale C₀ C₁ depth * overhead : Nat) :=
  RotationBST.Combo.Family.combine depth overhead C₀ C₁ capacity inputs charges well nonempty size fields oldData

theorem minimum_policy {ι : Type} [Fintype ι] [Nonempty ι] {saved : Tree}
    (overhead C₀ C₁ : Nat) (inputs : ι → Algorithm saved) (charges : ι → Charge)
    (well : ∀ i, Analysis.WellBehaved (inputs i).worker saved.size overhead C₀ C₁ (fun _ => charges i))
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ output : Algorithm saved,
      Guarantees output (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead)
        C₀ (C₁ + Nat.clog 2 (Fintype.card ι)) (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι))) charges ∧
      ∀ side xs, (∀ x ∈ xs, x < saved.size) →
        ∃ final cost, Worker.Requests output.worker side (output.worker.restart side) xs final cost ∧
          (cost : ℝ) ≤ (chargeScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) : ℝ) * minimum charges xs +
            (overheadScale C₀ C₁ (Nat.clog 2 (Fintype.card ι)) * overhead : Nat) :=
  RotationBST.Combo.Family.minimum_policy overhead C₀ C₁ inputs charges well nonempty size fields oldData

end RotationBST.Combo.Family.Results

/-- info: abstract audit passed for `RotationBST.Combo.Family.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Family.Results allowing [
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
  RotationBST.Algorithms.Combination.Family.Definitions.Abstract]
