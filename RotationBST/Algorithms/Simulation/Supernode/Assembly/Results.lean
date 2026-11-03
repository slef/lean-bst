module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Attachment

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

/-- info: abstract audit passed for `RotationBST.Arboral.Online.Supernode.Assembly.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Online.Supernode.Assembly.Results allowing [
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
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Defs,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Structures.Treap.Abstract,
  RotationBST.Models.Region.Abstract,
  RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Layer.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Nested.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Ranks.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Select.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Assembly.Defs]
