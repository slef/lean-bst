module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded.Lifetime.Results

/-- Splitting one interval pays for itself and passes all remaining budget to
its two descendants. No fresh allowance is introduced by a subsequent row. -/
theorem split_budget {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    let result := split state rank
    result.cost + intervalCredit result.left + intervalCredit result.right ≤ intervalCredit (some state) :=
  split_intervalCredit valid rank existsKey

/-- Arbitrarily interleaved partial plans preserve reusable leaf states and
have linear cumulative rotation cost over the original interval's lifetime. -/
theorem lifetime {input : Option State} {output : Partitioned} {cost : Nat}
    (steps : Refinement (.leaf input) output cost) (valid : IntervalValid input) :
    output.Valid ∧ Rotations (intervalTree input) output.tree cost ∧
      cost + output.credit ≤ intervalCredit input ∧
      cost + output.credit ≤ 6014 * (intervalTree input).size :=
  ⟨(steps.spec valid).1, (steps.spec valid).2.1, (steps.spec valid).2.2, steps.linear valid⟩

end RotationBST.SplitTree.Multiway.Finger.TwoEnded.Lifetime.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.TwoEnded.Lifetime.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.TwoEnded.Lifetime.Results allowing [
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
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs,
  RotationBST.Structures.SplitTree.Accounting.Abstract,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Defs]
