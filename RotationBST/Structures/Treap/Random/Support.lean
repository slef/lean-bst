module

public import RotationBST.Structures.Treap.Random.Average
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Treap.Random

theorem isOrder_cons {s : Finset Nat} {x : Nat} {xs : List Nat}
    (hx : x ∈ s) (h : IsOrder (s.erase x) xs) : IsOrder s (x :: xs) := by
  constructor
  · apply List.nodup_cons.mpr
    refine ⟨?_, h.1⟩
    intro hx'
    have hm : x ∈ xs.toFinset := List.mem_toFinset.mpr hx'
    rw [h.2] at hm
    exact Finset.notMem_erase x s hm
  · simp only [List.toFinset_cons, h.2, Finset.insert_erase hx]

/-- Expectations only depend on values at genuine priority orders. -/
theorem average_mono (w : Nat → ℝ) (s : Finset Nat) (f g : List Nat → ℝ)
    (hw : ∀ x ∈ s, 0 < w x) (h : ∀ xs, IsOrder s xs → f xs ≤ g xs) :
    average w s f ≤ average w s g := by
  induction s using Finset.strongInduction generalizing f g with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [average_step w s f hs, average_step w s g hs]
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos (hw x hx) (mass_pos w s hs hw)))
      apply ih (s.erase x) (Finset.erase_ssubset hx)
      · exact fun k hk => hw k (Finset.mem_of_mem_erase hk)
      · intro xs hxs
        exact h (x :: xs) (isOrder_cons hx hxs)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [average_empty] using h [] (by simp [IsOrder])

theorem average_strictMono (w : Nat → ℝ) (s : Finset Nat) (f g : List Nat → ℝ)
    (hw : ∀ x ∈ s, 0 < w x) (h : ∀ xs, IsOrder s xs → f xs < g xs) :
    average w s f < average w s g := by
  induction s using Finset.strongInduction generalizing f g with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [average_step w s f hs, average_step w s g hs]
      apply Finset.sum_lt_sum_of_nonempty hs
      intro x hx
      apply mul_lt_mul_of_pos_left _ (div_pos (hw x hx) (mass_pos w s hs hw))
      apply ih (s.erase x) (Finset.erase_ssubset hx)
      · exact fun k hk => hw k (Finset.mem_of_mem_erase hk)
      · intro xs hxs
        exact h (x :: xs) (isOrder_cons hx hxs)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simpa only [average_empty] using h [] (by simp [IsOrder])

/-- Finite probabilistic method: a supported order attains at most the mean. -/
theorem exists_order_le_average (w : Nat → ℝ) (s : Finset Nat) (f : List Nat → ℝ)
    (hw : ∀ x ∈ s, 0 < w x) :
    ∃ xs, IsOrder s xs ∧ f xs ≤ average w s f := by
  by_contra! h
  have hh := average_strictMono w s (fun _ => average w s f) f hw h
  rw [average_const w s _ hw] at hh
  exact lt_irrefl _ hh

end RotationBST.Treap.Random
