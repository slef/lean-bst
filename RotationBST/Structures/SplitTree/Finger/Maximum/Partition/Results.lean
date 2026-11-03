module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.HeightLoss

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Complete.Results

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

end RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Complete.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Complete.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Complete.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs]
