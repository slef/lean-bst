module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Layer.Update
public import RotationBST.Models.Region.View.Defs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open SplitTree.Multiway.Finger.TwoEnded

/-- Creation of a current-row supernode pays for all future splits once. Its
untouched gaps keep their exact trees and offsets, irrespective of their sizes. -/
theorem create_supernode {n time : Nat} {P : Finset Point} (history : History n time P)
    (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat)
    (gapHeaps : ∀ hole ∈ Region.holes (withGaps shape gaps offset) lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    let input := initialInterval shape.size
    let source := withGaps shape gaps offset
    let target := withGaps (intervalTree input) gaps offset
    IntervalValid input ∧ ∃ cost,
      Rotations source.tree target.tree cost ∧ Region.Same source target lo ∧
      Layer (P ∪ row time (Region.keys source lo)) (time : WithBot Nat) target lo ∧
      cost + intervalCredit input ≤ 6016 * (Region.keys source lo).card := by
  refine ⟨initialInterval_valid _, ?_⟩
  obtain ⟨cost, steps, budget⟩ := initialInterval_budget shape
  have same := withGaps_same steps gaps offset lo
  refine ⟨cost, (withGaps_rotations steps gaps offset).1, same,
    Layer.promote_rearranged history same gapHeaps, ?_⟩
  simpa only [Region.keys_card, withGaps_size] using budget

end RotationBST.Geometric.Online.Supernode
