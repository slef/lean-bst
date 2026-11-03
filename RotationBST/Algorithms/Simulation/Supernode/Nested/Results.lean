module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Initial
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Promotion
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Retention

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode.Nested.Results

/-- Every valid nested state realizes a last-touch heap over the full BST. -/
theorem heap {P : Finset Point} {lo : Nat} {state : Nested} (valid : Represents P lo state) :
    Heap (fun key => OrderDual.toDual (lastTouch P key)) state.tree lo := valid.heap

/-- A concrete initial represented state exists for every universe size. All
keys initially belong to one bottom-priority supernode, with empty child gaps. -/
theorem initial (n : Nat) : Represents ∅ 0 (initialNested n) ∧ (initialNested n).tree.size = n :=
  ⟨initialNested_represents n, initialNested_size n⟩

/-- A row missing an interval preserves its entire nested representation. -/
theorem untouched {time : Nat} {P : Finset Point} {keys : Finset Nat}
    {lo : Nat} {state : Nested} (valid : Represents P lo state)
    (misses : ∀ key, lo ≤ key → key < lo + state.tree.size → key ∉ keys) :
    Represents (P ∪ row time keys) lo state := valid.untouched misses

/-- Promote an assembled outer layer while retaining its recursively represented
children. The row consists exactly of the outer active keys. -/
theorem promote {n time : Nat} {P : Finset Point} (history : History n time P)
    (lo : Nat) (state : Split.Multiway.Finger.TwoEnded.State) (children : List Nested)
    (balanced : state.HeightValid) (arity : children.length = state.size + 1)
    (subtrees : ∀ i : Fin children.length,
      Represents P
        (lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val)
        children[i]) :
    Represents (P ∪ row time (Region.keys (nestedRegion state children) lo)) lo (.layer state children) :=
  Represents.promote history lo state children balanced arity subtrees

/-- A consecutive parent interval keeps its recursive representation when
stored in any valid shared state of the required size. Its children are
retained by an explicit list slice, with the correct absolute key offsets. -/
theorem retain {P : Finset Point} {lo : Nat}
    {state : Split.Multiway.Finger.TwoEnded.State} {children : List Nested}
    (valid : Represents P lo (.layer state children))
    (replacement : Split.Multiway.Finger.TwoEnded.State)
    (balanced : replacement.HeightValid) (first : Nat)
    (fits : first + replacement.size ≤ state.size) :
    Represents P
      (lo + first + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 first)
      (retainedNested replacement children first) :=
  valid.retain replacement balanced first fits

end RotationBST.Geometric.Online.Supernode.Nested.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.Supernode.Nested.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.Supernode.Nested.Results allowing [
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
  RotationBST.Algorithms.Simulation.Supernode.Nested.Defs]
