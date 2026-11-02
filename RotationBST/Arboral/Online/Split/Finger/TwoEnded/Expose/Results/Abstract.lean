module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Expose.Results

/-- Expose a requested key while retaining both output intervals and their
balanced pieces. Restoring shared-root height balance is a subsequent step. -/
theorem split {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    let result := expose state rank
    Access state.tree result.tree rank result.cost ∧ result.left.Valid ∧ result.right.Valid ∧
      result.left.tree.size = rank ∧ result.right.tree.size = state.size - 1 - rank :=
  ⟨expose_access state valid.1 valid.2.1 rank existsKey,
    (expose_valid state valid.1 valid.2.1 rank existsKey).1,
    (expose_valid state valid.1 valid.2.1 rank existsKey).2,
    expose_sizes state valid.1 valid.2.1 rank existsKey⟩

/-- Exposure has logarithmic amortized cost in the nearer endpoint distance,
with both output node reserves retained. This does not include normalization. -/
theorem amortized {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    let result := expose state rank
    result.cost + 2 * (result.left.nodes + result.right.nodes) ≤
      2 * (Fragment.shared state).nodes +
        170 * Nat.log2 (min rank (state.size - 1 - rank) + 1) + 285 :=
  expose_near_credit valid rank existsKey

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Expose.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Expose.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Abstract]
