module

public import RotationBST.Algorithms.Simulation.Supernode.Layer.Proofs
public import RotationBST.Structures.Treap.Projection
public import RotationBST.Models.Region.Holes

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- Promoting exactly a region's active keys forms a new equal-priority layer.
All gap heaps retain their old priorities; no gap reconstruction is needed. -/
theorem Layer.promote {n time : Nat} {P : Finset Point} (history : History n time P)
    (region : Region) (lo : Nat)
    (gaps : ∀ hole ∈ Region.holes region lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    Layer (P ∪ row time (Region.keys region lo)) (time : WithBot Nat) region lo := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact last_new_bound history _ _
  · intro key member
    exact last_new_current history member
  · intro hole member
    apply heap_congr _ _ (gaps hole member)
    intro key lower upper
    exact (last_new_untouched (Region.hole_disjoint member lower upper)).symm

/-- A split-and-rearrange operation may be followed by promotion of the active
keys. This changes their priority to the current row while preserving all gaps. -/
theorem Layer.promote_rearranged {n time : Nat} {P : Finset Point} (history : History n time P)
    {s t : Region} {lo : Nat} (same : Region.Same s t lo)
    (gaps : ∀ hole ∈ Region.holes s lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    Layer (P ∪ row time (Region.keys s lo)) (time : WithBot Nat) t lo := by
  rw [same.2.1]
  apply Layer.promote history
  intro hole member
  exact gaps hole (by rwa [same.2.2])

/-- Nonempty promoted active keys are exactly the interval's new canonical
supernode, so the semantic invariant agrees with the maintained representation. -/
theorem promoted_supernode {n time : Nat} {P : Finset Point} (history : History n time P)
    (region : Region) (lo : Nat) (nonempty : (Region.keys region lo).Nonempty) :
    supernodeKeys (P ∪ row time (Region.keys region lo)) lo (lo + region.tree.size) =
      Region.keys region lo := by
  have subset : Region.keys region lo ⊆ Finset.Ico lo (lo + region.tree.size) := by
    intro key member
    exact Finset.mem_Ico.mpr (Region.keys_bounds member)
  have intersection : Region.keys region lo ∩ Finset.Ico lo (lo + region.tree.size) = Region.keys region lo :=
    Finset.inter_eq_left.mpr subset
  have touched : (Region.keys region lo ∩ Finset.Ico lo (lo + region.tree.size)).Nonempty := by
    rwa [intersection]
  rw [supernode_row_keys history touched, intersection]

/-- A row avoiding an interval leaves its canonical supernode unchanged. -/
theorem supernode_untouched {time lo hi : Nat} {P : Finset Point} {keys : Finset Nat}
    (untouched : ∀ key ∈ Finset.Ico lo hi, key ∉ keys) :
    supernodeKeys (P ∪ row time keys) lo hi = supernodeKeys P lo hi := by
  have priority : supernodePriority (P ∪ row time keys) lo hi = supernodePriority P lo hi :=
    Finset.sup_congr rfl (fun key member => last_new_untouched (untouched key member))
  apply Finset.filter_congr
  intro key member
  rw [priority, last_new_untouched (untouched key member)]

/-- An untouched nested layer keeps both its equal-priority keys and gap heaps. -/
theorem Layer.untouched {time : Nat} {P : Finset Point} {keys : Finset Nat}
    {level : WithBot Nat} {region : Region} {lo : Nat} (valid : Layer P level region lo)
    (untouched : ∀ key, lo ≤ key → key < lo + region.tree.size → key ∉ keys) :
    Layer (P ∪ row time keys) level region lo := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [last_new_untouched (untouched (lo + x) (by omega) (by omega))]
    exact valid.1 x hx
  · intro key member
    have bounds := Region.keys_bounds member
    rw [last_new_untouched (untouched key bounds.1 bounds.2)]
    exact valid.2.1 key member
  · intro hole member
    have bounds := Region.holes_bounds member
    apply heap_congr _ _ (valid.2.2 hole member)
    intro key lower upper
    exact (last_new_untouched (untouched key (by omega) (by omega))).symm

end RotationBST.Geometric.Online.Supernode
