module

public import RotationBST.Structures.Treap.Random.Support
import Mathlib.Data.List.Basic

@[expose] public section
namespace RotationBST.Treap.Random

theorem firstIn_eq_iff (xs : List Nat) (s : Finset Nat) (a : Nat)
    (ha : a ∈ s) (sub : s ⊆ xs.toFinset) :
    firstIn s xs = some a ↔ ∀ b ∈ s, xs.idxOf a ≤ xs.idxOf b := by
  induction xs with
  | nil => have := sub ha; simp at this
  | cons x xs ih =>
    by_cases hx : x ∈ s
    · by_cases hax : a = x
      · subst a
        simp [firstIn, hx]
      · have hxa : x ≠ a := Ne.symm hax
        simp only [firstIn, hx, ↓reduceIte, Option.some.injEq]
        constructor
        · intro h; exact (hxa h).elim
        · intro h
          have hh := h x hx
          simpa [List.idxOf_cons] using hh
    · have hax : a ≠ x := by intro h; subst a; exact hx ha
      have sub' : s ⊆ xs.toFinset := by
        intro b hb
        have := sub hb
        simp only [List.toFinset_cons, Finset.mem_insert] at this
        exact this.resolve_left (by intro he; subst b; exact hx hb)
      simp only [firstIn, hx, ↓reduceIte]
      rw [ih sub']
      constructor <;> intro h b hb
      · have hbx : b ≠ x := by intro he; subst b; exact hx hb
        simpa [List.idxOf_cons, Ne.symm hax, Ne.symm hbx] using Nat.add_le_add_right (h b hb) 1
      · have hbx : b ≠ x := by intro he; subst b; exact hx hb
        have hh := h b hb
        simpa [List.idxOf_cons, Ne.symm hax, Ne.symm hbx] using hh

theorem order_idxOf_injective {u : Finset Nat} {xs : List Nat} (h : IsOrder u xs) :
    Set.InjOn xs.idxOf (u : Set Nat) := by
  intro a ha b _ he
  have ham : a ∈ xs := List.mem_toFinset.mp (by simpa [h.2] using ha)
  exact (List.idxOf_inj ham).mp he

theorem average_congr (w : Nat → ℝ) (s : Finset Nat) (f g : List Nat → ℝ)
    (hw : ∀ x ∈ s, 0 < w x) (h : ∀ xs, IsOrder s xs → f xs = g xs) :
    average w s f = average w s g := by
  apply le_antisymm
  · exact average_mono w s f g hw (fun xs hx => le_of_eq (h xs hx))
  · exact average_mono w s g f hw (fun xs hx => le_of_eq (h xs hx).symm)

end RotationBST.Treap.Random
