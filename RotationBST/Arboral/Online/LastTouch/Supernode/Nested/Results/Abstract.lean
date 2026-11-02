module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Initial
public import RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Promotion
public import RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Retention

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Nested.Results

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

end RotationBST.Arboral.Online.Supernode.Nested.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Nested.Results allowing [
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
  RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Abstract]
