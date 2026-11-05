module

public import RotationBST.Structures.Treap.Random.Average
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section
namespace RotationBST.Treap.Random

/-- Removing keys outside an observed subset does not bias its first choice:
the minimum-priority key has probability equal to its relative subset weight. -/
theorem firstProbability_eq (w : Nat → ℝ) (u s : Finset Nat) (a : Nat)
    (hw : ∀ x ∈ u, 0 < w x) (sub : s ⊆ u) (ha : a ∈ s) :
    firstProbability w u s a = w a / (∑ k ∈ s, w k) := by
  induction u using Finset.strongInduction generalizing s a with
  | H u ih =>
    have hu : u.Nonempty := ⟨a, sub ha⟩
    have hs : s.Nonempty := ⟨a, ha⟩
    have hW := mass_pos w u hu hw
    have hM := mass_pos w s hs (fun k hk => hw k (sub hk))
    have tail (x : Nat) (hx : x ∈ u) :
        average w (u.erase x) (fun xs => if firstIn s (x :: xs) = some a then 1 else 0) =
          if x ∈ s then (if x = a then 1 else 0) else w a / (∑ k ∈ s, w k) := by
      have hw' : ∀ k ∈ u.erase x, 0 < w k := fun k hk => hw k (Finset.mem_of_mem_erase hk)
      by_cases hxs : x ∈ s
      · simp only [firstIn, hxs, ↓reduceIte, Option.some.injEq]
        exact average_const w (u.erase x) _ hw'
      · simp only [firstIn, hxs, ↓reduceIte]
        apply ih (u.erase x) (Finset.erase_ssubset hx) s a hw' _ ha
        intro k hk
        exact Finset.mem_erase.mpr ⟨by intro he; subst k; exact hxs hk, sub hk⟩
    unfold firstProbability
    rw [average_step w u _ hu]
    have hsplit := Finset.sum_sdiff (f := fun x => w x / (∑ k ∈ u, w k) *
      average w (u.erase x) (fun xs => if firstIn s (x :: xs) = some a then 1 else 0)) sub
    rw [← hsplit]
    have hout : (∑ x ∈ u \ s, w x / (∑ k ∈ u, w k) *
        average w (u.erase x) (fun xs => if firstIn s (x :: xs) = some a then 1 else 0)) =
        ((∑ x ∈ u \ s, w x) / (∑ k ∈ u, w k)) * (w a / (∑ k ∈ s, w k)) := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [tail x (Finset.mem_sdiff.mp hx).1, ite_eq_right (Finset.mem_sdiff.mp hx).2]
    have hin : (∑ x ∈ s, w x / (∑ k ∈ u, w k) *
        average w (u.erase x) (fun xs => if firstIn s (x :: xs) = some a then 1 else 0)) =
        w a / (∑ k ∈ u, w k) := by
      calc
        _ = ∑ x ∈ s, w x / (∑ k ∈ u, w k) * (if x = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [tail x (sub hx), ite_eq_left hx]
        _ = _ := by simp [mul_ite, ha]
    rw [hout, hin]
    have hmass := Finset.sum_sdiff (f := w) sub
    field_simp [ne_of_gt hW, ne_of_gt hM]
    rw [hmass]
    ring

end RotationBST.Treap.Random
