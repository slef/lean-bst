module

public import RotationBST.Models.Region.Bounds
public import RotationBST.Structures.Treap.Abstract

@[expose] public section
namespace RotationBST.Geometric.Region
open Pointer.Lazy.Skeleton

theorem holes_bounds {s : Region} {lo : Nat} {e : Nat × Tree} (h : e ∈ holes s lo) :
    lo ≤ e.1 ∧ e.1 + e.2.size ≤ lo + s.tree.size := by
  induction s generalizing lo with
  | hole t => have he : e = (lo, t) := List.mem_singleton.mp h; subst e; exact ⟨le_rfl, le_rfl⟩
  | node l r il ir =>
    rcases List.mem_append.mp h with h | h
    · have := il h
      simp only [tree, Tree.size]; omega
    · have := ir h
      simp only [tree, Tree.size]; omega

theorem hole_disjoint {s : Region} {lo x : Nat} {e : Nat × Tree} (h : e ∈ holes s lo)
    (hlo : e.1 ≤ x) (hhi : x < e.1 + e.2.size) : x ∉ keys s lo := by
  induction s generalizing lo with
  | hole t => simp [keys]
  | node l r il ir =>
    intro hx
    rcases List.mem_append.mp h with h | h
    · have hb := holes_bounds h
      rcases Finset.mem_insert.mp hx with hx | hx
      · omega
      rcases Finset.mem_union.mp hx with hx | hx
      · exact il h hx
      · have := keys_bounds hx; omega
    · have hb := holes_bounds h
      rcases Finset.mem_insert.mp hx with hx | hx
      · omega
      rcases Finset.mem_union.mp hx with hx | hx
      · have := keys_bounds hx; omega
      · exact ir h hx

theorem heap_holes {α : Type} [LE α] (priority : Nat → α) (s : Region) (lo : Nat)
    (heap : Heap priority s.tree lo) : ∀ e ∈ holes s lo, Heap priority e.2 e.1 := by
  induction s generalizing lo with
  | hole t => intro e he; have heq := List.mem_singleton.mp he; subst e; exact heap
  | node l r il ir =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact il lo heap.2.1 e he
    · exact ir (lo + l.tree.size + 1) heap.2.2 e he

end RotationBST.Geometric.Region
