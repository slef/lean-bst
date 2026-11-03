module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Expose.Results

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

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Expose.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Expose.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Expose.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs]
