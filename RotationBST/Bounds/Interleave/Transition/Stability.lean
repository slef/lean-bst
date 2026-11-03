module

public import RotationBST.Bounds.Interleave.Transition.Top
public import RotationBST.Models.Region.Holes

@[expose] public section
namespace RotationBST.Tango
open Arboral Pointer.Lazy.Skeleton

private theorem covering_hole (s : Region) (lo low high : Nat)
    (lower : lo ≤ low) (upper : high ≤ lo + s.tree.size) (_nonempty : low < high)
    (untouched : ∀ x ∈ Arboral.Region.keys s lo, ¬ (low ≤ x ∧ x < high)) :
    ∃ e ∈ Arboral.Region.holes s lo, e.1 ≤ low ∧ high ≤ e.1 + e.2.size := by
  induction s generalizing lo with
  | hole t => exact ⟨(lo, t), List.mem_cons_self .., lower, upper⟩
  | node l r il ir =>
    have hroot := untouched (lo + l.tree.size) (Finset.mem_insert_self ..)
    by_cases hright : lo + l.tree.size < low
    · obtain ⟨e, he, hlo, hhi⟩ := ir (lo + l.tree.size + 1) (by omega)
        (by simp only [tree, Tree.size] at upper; omega)
        (fun x hx => untouched x (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)))
      exact ⟨e, List.mem_append_right _ he, hlo, hhi⟩
    · obtain ⟨e, he, hlo, hhi⟩ := il lo lower (by omega)
        (fun x hx => untouched x (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)))
      exact ⟨e, List.mem_append_left _ he, hlo, hhi⟩

private theorem topIn_hole (s : Region) (lo low high : Nat) (e : Nat × Tree)
    (hole : e ∈ Arboral.Region.holes s lo) (lower : e.1 ≤ low)
    (upper : high ≤ e.1 + e.2.size) (nonempty : low < high) :
    topIn s.tree lo low high = topIn e.2 e.1 low high := by
  induction s generalizing lo with
  | hole t => have he := List.mem_singleton.mp hole; subst e; rfl
  | node l r il ir =>
    rcases List.mem_append.mp hole with hole | hole
    · have hb := Arboral.Region.holes_bounds hole
      have h1 : ¬ lo + l.tree.size < low := by omega
      have h2 : high ≤ lo + l.tree.size := by omega
      simpa only [tree, topIn, ite_eq_right h1, ite_eq_left h2] using il lo hole
    · have hb := Arboral.Region.holes_bounds hole
      have h1 : lo + l.tree.size < low := by omega
      simpa only [tree, topIn, ite_eq_left h1] using ir (lo + l.tree.size + 1) hole

/-- An untouched interval top remains unchanged under a rooted rearrangement. -/
theorem topIn_stable {s u : Region} {lo low high root : Nat}
    (same : Arboral.Region.Same s u lo) (lower : lo ≤ low)
    (upper : high ≤ lo + s.tree.size) (nonempty : low < high)
    (top : topIn s.tree lo low high = some root) (untouched : root ∉ Arboral.Region.keys s lo) :
    topIn u.tree lo low high = some root := by
  have noneActive : ∀ x ∈ Arboral.Region.keys s lo, ¬ (low ≤ x ∧ x < high) := by
    intro x hx hbounds
    exact untouched (topIn_active s lo low high x root hx hbounds.1 hbounds.2 top)
  obtain ⟨e, he, hlo, hhi⟩ := covering_hole s lo low high lower upper nonempty noneActive
  have he' : e ∈ Arboral.Region.holes u lo := by rw [← same.2.2]; exact he
  rw [topIn_hole u lo low high e he' hlo hhi nonempty,
    ← topIn_hole s lo low high e he hlo hhi nonempty]
  exact top

/-- Wilber's transition point cannot change until it is touched. -/
theorem transition_stable {s u : Region} {low cut high point : Nat}
    (same : Arboral.Region.Same s u 0) (lower : low ≤ cut)
    (split : cut + 1 < high) (upper : high ≤ s.tree.size)
    (old : transition s.tree low cut high = some point)
    (untouched : point ∉ Arboral.Region.keys s 0) :
    transition u.tree low cut high = some point := by
  obtain ⟨root, top⟩ := topIn_exists s.tree 0 low high (Nat.zero_le _) (by simpa using upper) (by omega)
  have rb := topIn_bounds top
  by_cases active : root ∈ Arboral.Region.keys s 0
  · obtain ⟨newRoot, newTop⟩ := topIn_exists u.tree 0 low high (Nat.zero_le _)
      (by simpa only [Nat.zero_add, ← same.1] using upper) (by omega)
    have nb := topIn_bounds newTop
    have newActive : newRoot ∈ Arboral.Region.keys u 0 := topIn_active u 0 low high root newRoot
      (by rw [← same.2.1]; exact active) rb.2.2.1 rb.2.2.2 newTop
    have newActiveOld : newRoot ∈ Arboral.Region.keys s 0 := by rw [same.2.1]; exact newActive
    unfold transition at old ⊢
    rw [top] at old
    rw [newTop]
    dsimp only at old ⊢
    by_cases side : root ≤ cut
    · rw [ite_eq_left side] at old
      have newSide : newRoot ≤ cut := by
        by_contra hn
        exact untouched (topIn_active s 0 (cut + 1) high newRoot point newActiveOld
          (by omega) nb.2.2.2 old)
      rw [ite_eq_left newSide]
      exact topIn_stable same (Nat.zero_le _) (by simpa using upper) split old untouched
    · rw [ite_eq_right side] at old
      have newSide : ¬ newRoot ≤ cut := by
        intro hn
        exact untouched (topIn_active s 0 low (cut + 1) newRoot point newActiveOld
          nb.2.2.1 (by omega) old)
      rw [ite_eq_right newSide]
      exact topIn_stable same (Nat.zero_le _) (by simp only [Nat.zero_add]; omega)
        (by omega) old untouched
  · have newTop := topIn_stable same (Nat.zero_le _) (by simpa using upper) (by omega) top active
    unfold transition at old ⊢
    rw [top] at old
    rw [newTop]
    dsimp only at old ⊢
    by_cases side : root ≤ cut
    · rw [ite_eq_left side] at old ⊢
      exact topIn_stable same (Nat.zero_le _) (by simpa using upper) split old untouched
    · rw [ite_eq_right side] at old ⊢
      exact topIn_stable same (Nat.zero_le _) (by simp only [Nat.zero_add]; omega)
        (by omega) old untouched

end RotationBST.Tango
