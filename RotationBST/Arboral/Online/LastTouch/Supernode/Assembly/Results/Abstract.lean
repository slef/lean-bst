module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Attachment

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Assembly.Results

/-- Parent selection materializes the split hierarchy into canonical retained
subtrees and performs exactly the splitter's counted rotations. Attached
child sizes do not enter this stage's cost bound. -/
theorem selection {P : Finset Point} {lo : Nat}
    {state : Split.Multiway.Finger.TwoEnded.State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (keys : Finset Nat) :
    (selectParent state children lo keys).1.Valid P lo ∧
      Rotations (Nested.layer state children).tree (selectParent state children lo keys).1.region.tree
        (selectParent state children lo keys).2 ∧
      (selectParent state children lo keys).2 ≤ 6014 * state.size :=
  selectParent_spec represented keys

/-- Exposed keys are exactly this row's parent keys, in full-BST coordinates. -/
theorem selected_keys {P : Finset Point} {lo : Nat}
    {state : Split.Multiway.Finger.TwoEnded.State} {children : List Nested}
    (represented : Represents P lo (.layer state children)) (keys : Finset Nat) :
    Region.keys (selectParent state children lo keys).1.region lo =
      keys ∩ Region.keys (nestedRegion state children) lo :=
  selectParent_keys represented keys

/-- Attach child executions inside the holes, preserving validity and adding
exactly their rotation counts. -/
theorem attachment {P Q : Finset Point} (expand : Nested → Nat → Assembly × Nat)
    (correct : ∀ state lo, Represents P lo state →
      (expand state lo).1.Valid Q lo ∧
        Rotations state.tree (expand state lo).1.region.tree (expand state lo).2)
    {assembly : Assembly} {lo : Nat} (valid : assembly.Valid P lo) :
    (assembly.fill expand lo).1.Valid Q lo ∧
      Rotations assembly.region.tree (assembly.fill expand lo).1.region.tree
        (assembly.fill expand lo).2 :=
  Assembly.fill_spec expand correct valid

end RotationBST.Arboral.Online.Supernode.Assembly.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Assembly.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Initialize.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Arboral.Definitions.Abstract,
  RotationBST.Arboral.Treap.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract,
  RotationBST.Arboral.View.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Layer.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Ranks.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Select.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Abstract]
