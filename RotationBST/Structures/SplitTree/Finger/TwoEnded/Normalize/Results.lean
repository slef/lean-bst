module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Accounting

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded.Normalize.Results

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

end RotationBST.SplitTree.Multiway.Finger.TwoEnded.Normalize.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.TwoEnded.Normalize.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.TwoEnded.Normalize.Results allowing [
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
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs]
