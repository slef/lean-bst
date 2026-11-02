module

public import RotationBST.Tango.Auxiliary.Lifting
public import RotationBST.Arboral.Treap.Regions.Bounds
public import RotationBST.Splay.Correctness

@[expose] public section
namespace RotationBST.Arboral.Region
open Pointer.Lazy.Skeleton

private theorem filter_lt_strict {S : Finset Nat} {x y : Nat} (hx : x ∈ S) (hxy : x < y) :
    (S.filter (· < x)).card < (S.filter (· < y)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz, by omega⟩
  · intro he
    have hm : x ∈ S.filter (· < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← he] at hm
    have := (Finset.mem_filter.mp hm).2
    omega

theorem index_injective {s : Region} {lo x y : Nat} (hx : x ∈ keys s lo) (hy : y ∈ keys s lo)
    (h : index s lo x = index s lo y) : x = y := by
  by_cases hxy : x < y
  · have := filter_lt_strict hx hxy
    unfold index at h
    omega
  · by_cases hyx : y < x
    · have := filter_lt_strict hy hyx
      unfold index at h
      omega
    · omega

theorem index_valid {s : Region} {lo x : Nat} (hx : x ∈ keys s lo) : index s lo x < s.size := by
  rw [← keys_card s lo]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hm : x ∈ (keys s lo).filter (· < x) := by rw [he]; exact hx
  have := (Finset.mem_filter.mp hm).2
  omega

theorem index_root (l r : Region) (lo : Nat) : index (.node l r) lo (lo + l.tree.size) = l.size := by
  have he : (keys (.node l r) lo).filter (· < lo + l.tree.size) = keys l lo := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · omega
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · have := keys_bounds hx; omega
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hx),
        (keys_bounds hx).2⟩
  unfold index
  rw [he, keys_card]

/-- A local auxiliary access lifts at exactly the same rotation cost, even if
its leaves hold arbitrarily large unrelated trees. -/
theorem lift_access {s : Region} {target : Tree} {x cost : Nat}
    (hx : x ∈ keys s 0) (access : Access (shape s) target (index s 0 x) cost) :
    ∃ u : Region, shape u = target ∧ s.fringe = u.fringe ∧ Access s.tree u.tree x cost := by
  obtain ⟨u, hu, hf, rotations⟩ := lift_rotations access.1 s rfl
  have same := same_of_fringe hf 0
  cases u with
  | hole t =>
    have ht : target = .nil := hu.symm
    rw [ht] at access
    exact False.elim access.2
  | node l r =>
    have localRoot : l.size = index s 0 x := by
      have h := access.2
      rw [← hu] at h
      simpa only [shape, shape_size] using h
    have rootMem : l.tree.size ∈ keys s 0 := by
      rw [same.2.1]
      simpa only [keys, Nat.zero_add] using Finset.mem_insert_self (0 + l.tree.size)
        (keys l 0 ∪ keys r (0 + l.tree.size + 1))
    have rootIndex : index s 0 l.tree.size = l.size := by
      unfold index
      rw [same.2.1]
      simpa only [index, Nat.zero_add] using index_root l r 0
    have rootKey : x = l.tree.size := index_injective hx rootMem (localRoot.symm.trans rootIndex.symm)
    exact ⟨.node l r, hu, hf, rotations, rootKey.symm⟩

/-- Splay is a correct auxiliary-tree search implementation with exact global
rotation accounting; the analysis may use only the small active shape. -/
theorem auxiliary_splay (s : Region) (x : Nat) (hx : x ∈ keys s 0) :
    ∃ u : Region, shape u = (Splay.run (shape s) (index s 0 x)).1 ∧ s.fringe = u.fringe ∧
      Access s.tree u.tree x (Splay.run (shape s) (index s 0 x)).2 := by
  apply lift_access hx
  exact (Splay.run_correct _ _ (by rw [shape_size]; exact index_valid hx)).1

end RotationBST.Arboral.Region
