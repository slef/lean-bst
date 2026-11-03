module

public import RotationBST.Models.Region.View.Abstract
public import RotationBST.Models.Region.Bounds
public import RotationBST.Structures.Treap.Abstract

@[expose] public section
namespace RotationBST.Region
open Geometric
open Pointer.Lazy.Skeleton

/-- A rooted region containing `b` contains a common ancestor between `a` and
`b`; heap order bounds that ancestor's priority by `a`'s. -/
theorem between_ancestor {α : Type} [LE α] (priority : Nat → α)
    (s : Region) (lo a b : Nat) (heap : Heap priority s.tree lo)
    (alo : lo ≤ a) (ahi : a < lo + s.tree.size) (hb : b ∈ keys s lo) :
    ∃ c ∈ keys s lo, min a b ≤ c ∧ c ≤ max a b ∧ priority c ≤ priority a := by
  induction s generalizing lo with
  | hole t => simp [keys] at hb
  | node l r il ir =>
    have root : priority (lo + l.tree.size) ≤ priority a := by
      have h := heap.1 (a - lo) (by simp only [tree, Tree.size] at ahi; omega)
      have he : lo + (a - lo) = a := by omega
      simpa only [he] using h
    have rootCase (between : min a b ≤ lo + l.tree.size ∧ lo + l.tree.size ≤ max a b) :
        ∃ c ∈ keys (.node l r) lo, min a b ≤ c ∧ c ≤ max a b ∧ priority c ≤ priority a :=
      ⟨lo + l.tree.size, Finset.mem_insert_self .., between.1, between.2, root⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact rootCase ⟨min_le_right _ _, le_max_right _ _⟩
    rcases Finset.mem_union.mp hb with hb | hb
    · have hbb := keys_bounds hb
      by_cases ha : a < lo + l.tree.size
      · obtain ⟨c, hc, h1, h2, h3⟩ := il lo heap.2.1 alo ha hb
        exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_union_left _ hc), h1, h2, h3⟩
      · exact rootCase ⟨by omega, by omega⟩
    · have hbb := keys_bounds hb
      by_cases ha : lo + l.tree.size < a
      · obtain ⟨c, hc, h1, h2, h3⟩ := ir (lo + l.tree.size + 1) heap.2.2
          (by omega) (by simp only [tree, Tree.size] at ahi; omega) hb
        exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_union_right _ hc), h1, h2, h3⟩
      · exact rootCase ⟨by omega, by omega⟩

end RotationBST.Region
