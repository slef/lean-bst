module

public import RotationBST.Structures.Treap.Abstract
public import RotationBST.Models.Geometric.Rectangle

@[expose] public section
namespace RotationBST.Geometric

theorem nextTouch_le {P : Finset Point} {time key future : Nat}
    (hp : (key, future) ∈ P) (ht : time ≤ future) : nextTouch P time key ≤ future := by
  exact Finset.min_le (Finset.mem_image.mpr
    ⟨(key, future), Finset.mem_filter.mpr ⟨hp, rfl, ht⟩, rfl⟩)

theorem le_nextTouch {P : Finset Point} {time key : Nat} {bound : WithTop Nat}
    (h : ∀ future, (key, future) ∈ P → time ≤ future → bound ≤ future) :
    bound ≤ nextTouch P time key := by
  apply Finset.le_min
  intro future hf
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨hp, hx, ht⟩ := Finset.mem_filter.mp hp
  apply h p.2 _ ht
  simpa only [← hx, Prod.eta] using hp

theorem nextTouch_mono (P : Finset Point) {time later : Nat} (h : time ≤ later) (key : Nat) :
    nextTouch P time key ≤ nextTouch P later key := by
  apply le_nextTouch
  intro future hp ht
  exact nextTouch_le hp (h.trans ht)

theorem nextTouch_current {P : Finset Point} {time key : Nat} (h : (key, time) ∈ P) :
    nextTouch P time key = time := by
  apply le_antisymm (nextTouch_le h le_rfl)
  apply le_nextTouch
  intro future _ ht
  exact_mod_cast ht

theorem nextTouch_unchanged {P : Finset Point} {time key : Nat}
    (h : (key, time) ∉ P) : nextTouch P (time + 1) key = nextTouch P time key := by
  apply le_antisymm
  · apply le_nextTouch
    intro future hp ht
    have hne : future ≠ time := by rintro rfl; exact h hp
    exact nextTouch_le hp (by omega)
  · exact nextTouch_mono P (Nat.le_succ time) key

/-- The geometric fact that prevents a newly rearranged touched node from
sinking below an untouched fringe child in the offline treap construction. -/
theorem adjacent_nextTouch {P : Finset Point} {time a b : Nat}
    (sat : ASS P) (ha : (a, time) ∈ P) (different : a ≠ b)
    (adjacent : RowAdjacent P time a b) :
    nextTouch P (time + 1) a ≤ nextTouch P (time + 1) b := by
  apply le_nextTouch
  intro future hb ht
  obtain ⟨p, hp, hpa, _, hr, side⟩ := side_witness sat ha hb different (by omega)
  have hxlo := hr.1
  have hxhi := hr.2.1
  have hylo := hr.2.2.1
  have hyhi := hr.2.2.2
  have hpy : p.2 ≠ time := by
    intro heq
    have hpx : p.1 = a := adjacent p.1 (by simpa only [← heq, Prod.eta] using hp) hxlo hxhi
    exact hpa (Prod.ext hpx heq)
  have hpx : p.1 = a := side.resolve_right hpy
  have hmem : (a, p.2) ∈ P := by simpa only [← hpx, Prod.eta] using hp
  have hn := nextTouch_le hmem (show time + 1 ≤ p.2 by omega)
  exact hn.trans (by exact_mod_cast (show p.2 ≤ future by omega))

end RotationBST.Geometric
