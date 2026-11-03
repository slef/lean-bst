module

public import RotationBST.Models.Region.View.Ancestor
public import RotationBST.Models.Region.View.History
public import RotationBST.Models.Region.Holes
public import RotationBST.Models.Region.Fringe
public import RotationBST.Structures.Treap.Projection

@[expose] public section
namespace RotationBST.Arboral
open Pointer.Lazy.Skeleton

/-- A rooted set of touches in a latest-touch heap completes an ASS row. -/
theorem region_ass {n time : Nat} {P : Finset Point} (sat : ASS P)
    (hist : History n time P) (s : Region) (hsize : s.tree.size = n)
    (heap : HistoryHeap P s.tree) : ASS (P ∪ row time (Region.keys s 0)) := by
  have cross : ∀ a ∈ P, ∀ b ∈ row time (Region.keys s 0), a.1 ≠ b.1 →
      ∃ p ∈ P ∪ row time (Region.keys s 0), p ≠ a ∧ p ≠ b ∧ Rectangle a b p := by
    intro a ha b hb hx
    obtain ⟨hbkey, hbtime⟩ := (mem_row b time _).mp hb
    have hat := (hist a ha).2
    by_cases hakey : a.1 ∈ Region.keys s 0
    · refine ⟨(a.1, time), Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hakey, rfl⟩),
        ?_, ?_, ?_⟩
      · intro he; have := congrArg (fun p : Point => p.2) he; simp only at this; omega
      · intro he; have he' := congrArg (fun p : Point => p.1) he; exact hx he'
      · exact ⟨min_le_left _ _, le_max_left _ _, by omega, by omega⟩
    · obtain ⟨c, hc, hclo, hchi, hpriority⟩ := Region.between_ancestor
        (fun key => OrderDual.toDual (lastTouch P key)) s 0 a.1 b.1 heap
        (Nat.zero_le _) (by simpa only [Nat.zero_add, hsize] using (hist a ha).1) hbkey
      have hca : c ≠ a.1 := by intro he; exact hakey (he ▸ hc)
      have hlast : (a.2 : WithBot Nat) ≤ lastTouch P c :=
        (touch_le_last (by simpa only [Prod.eta] using ha)).trans hpriority
      obtain ⟨future, hp, hfuture⟩ := last_witness hlast
      have hft := (hist (c, future) hp).2
      refine ⟨(c, future), Finset.mem_union_left _ hp, ?_, ?_, ?_⟩
      · intro he; exact hca (congrArg Prod.fst he)
      · intro he; have := congrArg Prod.snd he; simp only at this; omega
      · exact ⟨hclo, hchi, by omega, by omega⟩
  intro a ha b hb hx hy
  rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨p, hp, hpa, hpb, hr⟩ := sat a ha b hb hx hy
    exact ⟨p, Finset.mem_union_left _ hp, hpa, hpb, hr⟩
  · exact cross a ha b hb hx
  · obtain ⟨p, hp, hpb, hpa, hr⟩ := cross b hb a ha (Ne.symm hx)
    exact ⟨p, hp, hpa, hpb, (rectangle_symm b a p).mp hr⟩
  · exact (hy (((mem_row a time _).mp ha).2.trans ((mem_row b time _).mp hb).2.symm)).elim

private theorem new_heap {n time : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (s : Region) (lo : Nat)
    (active : ∀ x ∈ Region.keys s lo, x ∈ keys)
    (fringe : ∀ e ∈ Region.holes s lo,
      Heap (fun x => OrderDual.toDual (lastTouch (P ∪ row time keys) x)) e.2 e.1) :
    Heap (fun x => OrderDual.toDual (lastTouch (P ∪ row time keys) x)) s.tree lo := by
  induction s generalizing lo with
  | hole t => exact fringe (lo, t) (List.mem_cons_self ..)
  | node l r il ir =>
    refine ⟨?_, il lo ?_ ?_, ir (lo + l.tree.size + 1) ?_ ?_⟩
    · intro x _
      change lastTouch (P ∪ row time keys) (lo + x) ≤ lastTouch (P ∪ row time keys) (lo + l.tree.size)
      rw [last_new_current hist (active _ (Finset.mem_insert_self ..))]
      exact last_new_bound hist keys _
    · intro x hx; exact active x (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
    · intro e he; exact fringe e (List.mem_append_left _ he)
    · intro x hx; exact active x (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    · intro e he; exact fringe e (List.mem_append_right _ he)

/-- Rearranging all current-row keys preserves the latest-touch heap invariant. -/
theorem region_history_heap {n time : Nat} {P : Finset Point}
    (hist : History n time P) {s u : Region} (same : Region.Same s u 0)
    (heap : HistoryHeap P s.tree) :
    HistoryHeap (P ∪ row time (Region.keys s 0)) u.tree := by
  apply new_heap hist u 0
  · intro x hx; rw [same.2.1]; exact hx
  · intro e he
    rw [← same.2.2] at he
    have old := Region.heap_holes (fun x => OrderDual.toDual (lastTouch P x)) s 0 heap e he
    apply heap_congr _ _ old
    intro x hlo hhi
    exact (last_new_untouched (Region.hole_disjoint he hlo hhi)).symm

end RotationBST.Arboral
