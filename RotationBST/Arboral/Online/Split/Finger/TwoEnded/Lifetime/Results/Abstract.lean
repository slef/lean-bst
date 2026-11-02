module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Lifetime.Results

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

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Lifetime.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Lifetime.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Abstract,
  RotationBST.Arboral.Online.Split.Accounting.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Abstract]
