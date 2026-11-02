module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Partition.HeightLoss

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Partition.Complete.Results

/-- Split from the minimum finger, including repair of the enclosing context.
Both outputs are balanced and retain their finger representations. This is
correctness with an exact rotation count; the amortized bound is below. -/
theorem split {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let result := splitFromMinimum t rank
    Access (binaryView t).tree (splitView result) rank result.cost ∧ result.Valid ∧
      result.left.tree.size = rank ∧ result.right.tree.size = t.size - rank - 1 :=
  ⟨splitFromMinimum_access valid rank existsKey, splitFromMinimum_balance valid rank existsKey,
    splitFromMinimum_sizes valid rank existsKey⟩

/-- Complete splitting has logarithmic amortized cost in the distance from the
minimum. Both output node reserves are retained in the inequality. -/
theorem amortized {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let result := splitFromMinimum t rank
    result.cost + 2 * (result.left.tree.nodes + result.right.tree.nodes) ≤
      2 * t.nodes + 85 * (Nat.log2 (rank + 1) + 1) + 29 :=
  splitFromMinimum_credit valid rank existsKey

/-- A height-lowering split releases enough node reserve to pay for rebuilding
at the original height, apart from logarithmic endpoint work. -/
theorem height_loss {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size)
    (lost : (splitFromMinimum t rank).right.height < h) :
    let result := splitFromMinimum t rank
    result.left.tree.nodes + result.right.tree.nodes + h ≤
      t.nodes + 30 * (Nat.log2 (rank + 1) + 1) + 4 :=
  splitFromMinimum_height_loss valid rank existsKey lost

end RotationBST.Arboral.Split.Multiway.Finger.Partition.Complete.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Partition.Complete.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.Partition.Abstract]
