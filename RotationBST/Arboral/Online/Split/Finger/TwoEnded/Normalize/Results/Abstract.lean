module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Accounting

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Normalize.Results

/-- Complete splitting returns reusable height-valid intervals, including empty
ones, with exact rotations and sizes. -/
theorem complete {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    let result := split state rank
    Access state.tree result.tree rank result.cost ∧
      IntervalValid result.left ∧ IntervalValid result.right ∧
      (intervalTree result.left).size = rank ∧
      (intervalTree result.right).size = state.size - 1 - rank :=
  ⟨split_access valid rank existsKey, (split_valid valid rank existsKey).1,
    (split_valid valid rank existsKey).2, split_sizes valid rank existsKey⟩

/-- Normalize one output, with an explicit bound on newly allocated reserves. -/
theorem restore (fragment : Fragment) (valid : fragment.Valid) :
    let result := normalize fragment
    IntervalValid result.1 ∧ Rotations fragment.tree (intervalTree result.1) result.2 ∧
      intervalNodes result.1 ≤ fragment.nodes + result.2 + 2 :=
  ⟨(normalize_spec fragment valid).1, (normalize_spec fragment valid).2, normalize_nodes fragment⟩

/-- A single-finger output can be normalized with linear cost in its height. -/
theorem endpoint_cost (piece : Multiway.Partition.Piece) (valid : piece.Valid) :
    (normalize (.minimum piece)).2 ≤ 9 * piece.height ∧
      (normalize (.maximum piece)).2 ≤ 9 * piece.height :=
  ⟨normalize_minimum_cost piece valid, normalize_maximum_cost piece valid⟩

/-- Normalization allocates only logarithmically many nodes beyond those
already stored in the exposed intervals. -/
theorem local_allocation {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    intervalNodes (split state rank).left + intervalNodes (split state rank).right ≤
      (expose state rank).left.nodes + (expose state rank).right.nodes +
        3 * Nat.log2 (chosenDistance state rank + 1) + 10 :=
  split_normalization_nodes valid rank existsKey

/-- All rotations of complete splitting are paid by logarithmic nearer-endpoint
work and the node reserve; both output reserves remain available. -/
theorem amortized {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    let result := split state rank
    result.cost + 14 * (intervalNodes result.left + intervalNodes result.right) ≤
      14 * (Fragment.shared state).nodes +
        3000 * (Nat.log2 (min rank (state.size - 1 - rank) + 1) + 1) :=
  split_credit valid rank existsKey

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Normalize.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Normalize.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Abstract]
