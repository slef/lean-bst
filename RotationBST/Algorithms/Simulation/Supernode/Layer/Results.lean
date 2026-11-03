module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Layer.Update

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Layer.Results

/-- A canonical root supernode with recursively heap-ordered gaps represents
a last-touch heap, independently of the active keys' BST shape. -/
theorem canonical {P : Finset Point} {region : Region} {lo : Nat}
    (keys : Region.keys region lo = supernodeKeys P lo (lo + region.tree.size))
    (gaps : ∀ hole ∈ Region.holes region lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    Layer P (supernodePriority P lo (lo + region.tree.size)) region lo ∧
      Heap (fun key => OrderDual.toDual (lastTouch P key)) region.tree lo :=
  ⟨Layer.canonical keys gaps, (Layer.canonical keys gaps).heap⟩

/-- Supernode rotations preserve the layer invariant, all absolute active keys,
and every untouched gap with its offset, at exactly the original rotation cost. -/
theorem rearrange {P : Finset Point} {level : WithBot Nat} {s t : Tree} {cost : Nat}
    (steps : Rotations s t cost) (gaps : Nat → Tree) (offset lo : Nat)
    (valid : Layer P level (withGaps s gaps offset) lo) :
    Rotations (withGaps s gaps offset).tree (withGaps t gaps offset).tree cost ∧
      Region.Same (withGaps s gaps offset) (withGaps t gaps offset) lo ∧
      Layer P level (withGaps t gaps offset) lo ∧
      Heap (fun key => OrderDual.toDual (lastTouch P key)) (withGaps t gaps offset).tree lo :=
  ⟨(withGaps_rotations steps gaps offset).1, withGaps_same steps gaps offset lo,
    Layer.rotate steps gaps offset lo valid⟩

/-- Promoting the active keys after rearrangement creates a current-row layer.
No key inside a retained gap is promoted or rearranged. -/
theorem promote {n time : Nat} {P : Finset Point} (history : History n time P)
    {s t : Region} {lo : Nat} (same : Region.Same s t lo)
    (gaps : ∀ hole ∈ Region.holes s lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    Layer (P ∪ row time (Region.keys s lo)) (time : WithBot Nat) t lo :=
  Layer.promote_rearranged history same gaps

/-- The promoted region represents exactly the new canonical supernode. -/
theorem promoted_keys {n time : Nat} {P : Finset Point} (history : History n time P)
    (region : Region) (lo : Nat) (nonempty : (Region.keys region lo).Nonempty) :
    supernodeKeys (P ∪ row time (Region.keys region lo)) lo (lo + region.tree.size) =
      Region.keys region lo := promoted_supernode history region lo nonempty

/-- A row missing an interval preserves its existing layer and canonical keys. -/
theorem untouched {time : Nat} {P : Finset Point} {keys : Finset Nat}
    {level : WithBot Nat} {region : Region} {lo : Nat} (valid : Layer P level region lo)
    (misses : ∀ key, lo ≤ key → key < lo + region.tree.size → key ∉ keys) :
    Layer (P ∪ row time keys) level region lo ∧
      supernodeKeys (P ∪ row time keys) lo (lo + region.tree.size) =
        supernodeKeys P lo (lo + region.tree.size) :=
  ⟨valid.untouched misses, supernode_untouched (fun key member =>
    misses key (Finset.mem_Ico.mp member).1 (Finset.mem_Ico.mp member).2)⟩

end RotationBST.Arboral.Online.Supernode.Layer.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Online.Supernode.Layer.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Online.Supernode.Layer.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Structures.Treap.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Layer.Defs]
