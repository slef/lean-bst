module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Layer.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Proofs
public import RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Regions

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Pointer.Lazy.Skeleton

/-- Equal-priority active keys may use any BST shape: ordering inside the
layer is independent of the lower-priority gap heaps. -/
theorem Layer.heap {P : Finset Point} {level : WithBot Nat} {region : Region} {lo : Nat}
    (valid : Layer P level region lo) :
    Heap (fun key => OrderDual.toDual (lastTouch P key)) region.tree lo := by
  induction region generalizing lo with
  | hole t => exact valid.2.2 (lo, t) (List.mem_singleton_self _)
  | node l r il ir =>
    have root := valid.2.1 (lo + l.tree.size) (Finset.mem_insert_self ..)
    refine ⟨?_, il ?_, ir ?_⟩
    · intro x hx
      change lastTouch P (lo + x) ≤ lastTouch P (lo + l.tree.size)
      rw [root]
      exact valid.1 x hx
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact valid.1 x (by change x < l.tree.size + 1 + r.tree.size; omega)
      · intro key member
        exact valid.2.1 key (Finset.mem_insert_of_mem (Finset.mem_union_left _ member))
      · intro gap member
        exact valid.2.2 gap (List.mem_append_left _ member)
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have bound := valid.1 (l.tree.size + 1 + x) (by change _ < l.tree.size + 1 + r.tree.size; omega)
        simpa only [Nat.add_assoc] using bound
      · intro key member
        exact valid.2.1 key (Finset.mem_insert_of_mem (Finset.mem_union_right _ member))
      · intro gap member
        exact valid.2.2 gap (List.mem_append_right _ member)

/-- The canonical maximal-priority supernode satisfies the layer invariant
once its gap subtrees have been recursively represented as heaps. -/
theorem Layer.canonical {P : Finset Point} {region : Region} {lo : Nat}
    (keys : Region.keys region lo = supernodeKeys P lo (lo + region.tree.size))
    (gaps : ∀ hole ∈ Region.holes region lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    Layer P (supernodePriority P lo (lo + region.tree.size)) region lo := by
  refine ⟨?_, ?_, gaps⟩
  · intro x hx
    exact supernode_priority_upper P (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  · intro key member
    rw [keys] at member
    exact (Finset.mem_filter.mp member).2

/-- Rearranging the layer preserves its invariant because absolute active
keys, gap offsets, and the gap trees themselves are unchanged. -/
theorem Layer.rearrange {P : Finset Point} {level : WithBot Nat} {s t : Region} {lo : Nat}
    (valid : Layer P level s lo) (same : Region.Same s t lo) : Layer P level t lo := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact valid.1 x (by rwa [same.1])
  · intro key member
    exact valid.2.1 key (by rwa [same.2.1])
  · intro gap member
    exact valid.2.2 gap (by rwa [same.2.2])

/-- Verified supernode split rotations preserve the enclosing last-touch heap. -/
theorem Layer.rotate {P : Finset Point} {level : WithBot Nat} {s t : Tree} {cost : Nat}
    (steps : Rotations s t cost) (gaps : Nat → Tree) (offset lo : Nat)
    (valid : Layer P level (withGaps s gaps offset) lo) :
    Layer P level (withGaps t gaps offset) lo ∧
      Heap (fun key => OrderDual.toDual (lastTouch P key)) (withGaps t gaps offset).tree lo := by
  have result := valid.rearrange (withGaps_same steps gaps offset lo)
  exact ⟨result, result.heap⟩

end RotationBST.Arboral.Online.Supernode
