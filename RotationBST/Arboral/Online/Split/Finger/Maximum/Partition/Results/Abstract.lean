module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.HeightLoss

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Maximum.Partition.Complete.Results

/-- Split from the maximum finger, including repair of the enclosing context.
Both outputs are balanced and retain their finger representations. This is
correctness with an exact rotation count; the amortized bound is below. -/
theorem split {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    let result := splitFromMaximum t distance
    Access (maximumView t).tree (maximumSplitView result) (t.size - 1 - distance) result.cost ∧ result.Valid ∧
      result.left.tree.size = t.size - 1 - distance ∧ result.right.tree.size = distance :=
  ⟨splitFromMaximum_access valid distance existsKey, splitFromMaximum_balance valid distance existsKey,
    splitFromMaximum_sizes valid distance existsKey⟩

/-- Complete splitting has logarithmic amortized cost in the distance from the
maximum. Both output node reserves are retained in the inequality. -/
theorem amortized {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    let result := splitFromMaximum t distance
    result.cost + 2 * (result.left.tree.nodes + result.right.tree.nodes) ≤
      2 * t.nodes + 85 * (Nat.log2 (distance + 1) + 1) + 29 :=
  splitFromMaximum_credit valid distance existsKey

/-- A height-lowering split releases enough node reserve to pay for rebuilding
at the original height, apart from logarithmic endpoint work. -/
theorem height_loss {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size)
    (lost : (splitFromMaximum t distance).left.height < h) :
    let result := splitFromMaximum t distance
    result.left.tree.nodes + result.right.tree.nodes + h ≤
      t.nodes + 30 * (Nat.log2 (distance + 1) + 1) + 4 :=
  splitFromMaximum_height_loss valid distance existsKey lost

end RotationBST.Arboral.Split.Multiway.Finger.Maximum.Partition.Complete.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Partition.Complete.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Abstract]
