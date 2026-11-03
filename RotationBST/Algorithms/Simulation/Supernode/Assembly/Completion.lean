module

public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Progress

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- If child extraction covers each hole's row keys, attaching those regions
covers the entire row interval. The bound restricts the recursive obligation
to smaller subtrees, as required by the extraction induction. -/
theorem Assembly.fill_keys {P : Finset Point} {keys : Finset Nat} {limit : Nat}
    (expand : Nested → Nat → Assembly × Nat)
    (execution : ∀ state lo, Represents P lo state →
      (expand state lo).1.Valid P lo ∧
        Rotations state.tree (expand state lo).1.region.tree (expand state lo).2)
    (complete : ∀ state lo, Represents P lo state → state.tree.size < limit →
      Region.keys (expand state lo).1.region lo = keys ∩ Finset.Ico lo (lo + state.tree.size))
    {assembly : Assembly} {lo : Nat} (valid : assembly.Valid P lo)
    (selected : Region.keys assembly.region lo ⊆ keys)
    (smaller : ∀ hole ∈ Region.holes assembly.region lo, hole.2.size < limit) :
    Region.keys (assembly.fill expand lo).1.region lo =
      keys ∩ Finset.Ico lo (lo + assembly.region.tree.size) := by
  induction assembly generalizing lo with
  | hole state =>
    exact complete state lo valid (smaller (lo, state.tree) (List.mem_singleton_self _))
  | node left right il ir =>
    have root : lo + left.region.tree.size ∈ keys :=
      selected (Finset.mem_insert_self _ _)
    have leftSelected : Region.keys left.region lo ⊆ keys := by
      intro key member
      exact selected (Finset.mem_insert_of_mem (Finset.mem_union_left _ member))
    have rightSelected : Region.keys right.region (lo + left.region.tree.size + 1) ⊆ keys := by
      intro key member
      exact selected (Finset.mem_insert_of_mem (Finset.mem_union_right _ member))
    have leftSmaller : ∀ hole ∈ Region.holes left.region lo, hole.2.size < limit := by
      intro hole member
      exact smaller hole (List.mem_append_left _ member)
    have rightSmaller : ∀ hole ∈ Region.holes right.region (lo + left.region.tree.size + 1), hole.2.size < limit := by
      intro hole member
      exact smaller hole (List.mem_append_right _ member)
    have l := il valid.1 leftSelected leftSmaller
    have r := ir valid.2 rightSelected rightSmaller
    have size := (Assembly.fill_spec expand execution valid.1).2.size_eq
    simp only [Assembly.fill, Assembly.region, Region.keys]
    rw [← size, l, r]
    ext key
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_inter, Finset.mem_Ico,
      Pointer.Lazy.Skeleton.tree, Tree.size]
    constructor
    · rintro (equal | ⟨member, bounds⟩ | ⟨member, bounds⟩)
      · subst key
        exact ⟨root, by omega, by omega⟩
      · exact ⟨member, by omega, by omega⟩
      · exact ⟨member, by omega, by omega⟩
    · rintro ⟨member, lower, upper⟩
      by_cases before : key < lo + left.region.tree.size
      · exact Or.inr (Or.inl ⟨member, by omega, before⟩)
      · by_cases equal : key = lo + left.region.tree.size
        · exact Or.inl equal
        · exact Or.inr (Or.inr ⟨member, by omega, by omega⟩)

end RotationBST.Geometric.Online.Supernode
