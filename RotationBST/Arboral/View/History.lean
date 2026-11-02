module

public import RotationBST.Arboral.View.Abstract
public import RotationBST.Arboral.Basic

@[expose] public section
namespace RotationBST.Arboral

theorem touch_le_last {P : Finset Point} {key time : Nat} (h : (key, time) ∈ P) :
    (time : WithBot Nat) ≤ lastTouch P key :=
  Finset.le_max (Finset.mem_image.mpr
    ⟨(key, time), Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩)

theorem last_le {P : Finset Point} {key time : Nat} (h : ∀ p ∈ P, p.2 ≤ time) :
    lastTouch P key ≤ (time : WithBot Nat) := by
  apply Finset.max_le
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  exact_mod_cast h p (Finset.mem_filter.mp hp).1

theorem last_witness {P : Finset Point} {key time : Nat}
    (h : (time : WithBot Nat) ≤ lastTouch P key) :
    ∃ future, (key, future) ∈ P ∧ time ≤ future := by
  have hn : lastTouch P key ≠ ⊥ := by
    intro he
    rw [he] at h
    exact WithBot.not_coe_le_bot time h
  obtain ⟨future, heq⟩ := WithBot.ne_bot_iff_exists.mp hn
  have hm := Finset.mem_of_max heq.symm
  obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hm
  obtain ⟨hp, hpx⟩ := Finset.mem_filter.mp hp
  refine ⟨future, ?_, ?_⟩
  · have he : p = (key, future) := Prod.ext hpx hpt
    simpa only [he] using hp
  · rw [← heq] at h
    exact_mod_cast h

theorem last_new_bound {n time : Nat} {P : Finset Point} (hist : History n time P)
    (keys : Finset Nat) (x : Nat) : lastTouch (P ∪ row time keys) x ≤ (time : WithBot Nat) := by
  apply last_le
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Nat.le_of_lt (hist p hp).2
  · exact le_of_eq ((mem_row p time keys).mp hp).2

theorem last_new_current {n time : Nat} {P : Finset Point} {keys : Finset Nat} {x : Nat}
    (hist : History n time P) (hx : x ∈ keys) :
    lastTouch (P ∪ row time keys) x = (time : WithBot Nat) := by
  apply le_antisymm (last_new_bound hist keys x)
  exact touch_le_last (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩))

theorem last_new_untouched {time : Nat} {P : Finset Point} {keys : Finset Nat} {x : Nat}
    (hx : x ∉ keys) : lastTouch (P ∪ row time keys) x = lastTouch P x := by
  have heq : (P ∪ row time keys).filter (fun p => p.1 = x) =
      P.filter (fun p => p.1 = x) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, mem_row]
    constructor
    · rintro ⟨hp | ⟨hk, _⟩, he⟩
      · exact ⟨hp, he⟩
      · exact (hx (he ▸ hk)).elim
    · rintro ⟨hp, he⟩
      exact ⟨Or.inl hp, he⟩
  unfold lastTouch
  rw [heq]

end RotationBST.Arboral
