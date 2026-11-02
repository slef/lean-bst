module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Partial.Results

/-- Execute current split choices and retain every stopped interval as a
valid reusable state, with the exact rotation count and unspent reserves. -/
theorem execute (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    let result := runPlan plan input
    result.1.Valid ∧ Rotations (intervalTree input) result.1.tree result.2 ∧
      result.2 + 14 * result.1.reserve ≤ 6014 * (intervalTree input).size :=
  ⟨(runPlan_spec plan input valid applicable).1, (runPlan_spec plan input valid applicable).2,
    runPlan_linear plan input valid applicable⟩

/-- Reserves at retained leaves remain available for subsequent splitting. -/
theorem accounting (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    let result := runPlan plan input
    result.2 + 14 * result.1.reserve ≤
      14 * intervalNodes input + 3000 * totalCharge result.1.tree :=
  runPlan_credit plan input valid applicable

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Partial.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Partial.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Abstract]
