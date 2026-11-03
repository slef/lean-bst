module

public import RotationBST.Models.Region.Basic

@[expose] public section
namespace RotationBST.Geometric.Region
open Pointer.Lazy.Skeleton

theorem keys_bounds {s : Region} {lo x : Nat} (h : x ∈ keys s lo) :
    lo ≤ x ∧ x < lo + s.tree.size := by
  induction s generalizing lo with
  | hole t => simp [keys] at h
  | node l r il ir =>
    rcases Finset.mem_insert.mp h with rfl | h
    · simp only [tree, Tree.size]; omega
    rcases Finset.mem_union.mp h with h | h
    · have := il h
      simp only [tree, Tree.size]; omega
    · have := ir h
      simp only [tree, Tree.size]; omega

theorem keys_card (s : Region) (lo : Nat) : (keys s lo).card = s.size := by
  induction s generalizing lo with
  | hole t => rfl
  | node l r il ir =>
    have notroot : lo + l.tree.size ∉ keys l lo ∪ keys r (lo + l.tree.size + 1) := by
      intro h
      rcases Finset.mem_union.mp h with h | h <;> have := keys_bounds h <;> omega
    have dis : Disjoint (keys l lo) (keys r (lo + l.tree.size + 1)) := by
      rw [Finset.disjoint_left]
      intro x hl hr
      have := keys_bounds hl
      have := keys_bounds hr
      omega
    simp only [keys, Finset.card_insert_of_notMem notroot,
      Finset.card_union_of_disjoint dis, il, ir, size]
    omega

theorem complete_children {P : Finset Point} {time lo : Nat} {l r : Region}
    (complete : ∀ x, x ∈ keys (.node l r) lo ↔
      (x, time) ∈ P ∧ lo ≤ x ∧ x < lo + (Pointer.Lazy.Skeleton.tree (.node l r)).size) :
    (∀ x, x ∈ keys l lo ↔ (x, time) ∈ P ∧ lo ≤ x ∧ x < lo + l.tree.size) ∧
    (∀ x, x ∈ keys r (lo + l.tree.size + 1) ↔ (x, time) ∈ P ∧
      lo + l.tree.size + 1 ≤ x ∧ x < lo + l.tree.size + 1 + r.tree.size) := by
  constructor
  · intro x
    constructor
    · intro hx
      have hp := (complete x).mp (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
      exact ⟨hp.1, keys_bounds hx⟩
    · rintro ⟨hp, hlo, hhi⟩
      have hx := (complete x).mpr ⟨hp, hlo, by simp only [tree, Tree.size]; omega⟩
      rcases Finset.mem_insert.mp hx with hx | hx
      · omega
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hx
      · have := keys_bounds hx; omega
  · intro x
    constructor
    · intro hx
      have hp := (complete x).mp (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
      exact ⟨hp.1, keys_bounds hx⟩
    · rintro ⟨hp, hlo, hhi⟩
      have hx := (complete x).mpr ⟨hp, by omega, by simp only [tree, Tree.size]; omega⟩
      rcases Finset.mem_insert.mp hx with hx | hx
      · omega
      rcases Finset.mem_union.mp hx with hx | hx
      · have := keys_bounds hx; omega
      · exact hx

end RotationBST.Geometric.Region
