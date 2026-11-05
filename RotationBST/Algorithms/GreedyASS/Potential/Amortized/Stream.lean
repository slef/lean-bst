module

public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Startup
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized
open Reference

theorem points_card (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (Virgin.points xs).card = rowCost greedySweep 0 ∅ xs := by
  have run := (fill_spec (greedyASS n) 0 ∅ xs
    (by simp [History]) ass_empty valid).2.2
  simpa [Virgin.points, greedyASS] using run

theorem points_card_snoc (n : Nat) (xs : List Nat) (x : Nat)
    (valid : ∀ y ∈ xs ++ [x], y < n) :
    (Virgin.points (xs ++ [x])).card = (Virgin.points xs).card + (Virgin.keys xs x).card := by
  have oldValid : ∀ y ∈ xs, y < n := fun y hy => valid y (List.mem_append_left _ hy)
  have history := Virgin.points_history n xs oldValid
  rw [Virgin.points_snoc]
  exact completion_card history (sweep_correct history (Unaccessed.points_satisfied xs oldValid)
    (valid x (by simp)))

theorem columns_snoc (xs : List Nat) (x : Nat) :
    ((Virgin.points (xs ++ [x])).image Prod.fst).card =
      ((Virgin.points xs).image Prod.fst).card +
        (unseenKeys (Virgin.points xs) (Virgin.keys xs x)).card := by
  rw [Virgin.points_snoc]
  exact columns_step _ _ _

/-- The complete telescoping bound retains final potential and exact
distinct-column charges. The startup term is paid once for the whole stream. -/
theorem stream (t : Tree) (lo : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.points xs).card + potential t lo xs ≤
      12 * leaves t + 24 * referenceCost t lo xs + 3 * ((Virgin.points xs).image Prod.fst).card := by
  induction xs using List.reverseRecOn with
  | nil => simp [potential_nil, Virgin.points, fill, referenceCost, edgeCost]
  | append_singleton xs next ih =>
    have oldValid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t :=
      fun x hx => valid x (List.mem_append_left _ hx)
    have counts := points_card_snoc (lo + leaves t) xs next (fun x hx => (valid x hx).2)
    have columns := columns_snoc xs next
    rcases List.eq_nil_or_concat xs with empty | ⟨prior, old, eq⟩
    · subst xs
      have bound := startup t lo next (valid next (by simp))
      have empty : Virgin.points [] = ∅ := rfl
      simp only [List.nil_append, empty, Finset.image_empty, Finset.card_empty, zero_add] at counts columns bound
      simp only [List.nil_append, referenceCost, List.length_singleton, edgeCost, Nat.add_zero]
      omega
    · rw [List.concat_eq_append] at eq
      subst xs
      have previous := ih oldValid
      have bound := step t lo prior old next valid
      simp only [referenceCost, List.length_append, List.length_singleton, edgeCost_snoc] at previous ⊢
      omega

/-- Every encountered column belongs to the reference interval. In
particular the startup allowance is independent of the rank offset. -/
theorem columns_bound (t : Tree) (lo : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t) :
    ((Virgin.points xs).image Prod.fst).card ≤ leaves t := by
  have subset : (Virgin.points xs).image Prod.fst ⊆ Finset.Ico lo (lo + leaves t) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Ico.mpr (Unaccessed.points_property _ xs valid p hp)
  simpa using Finset.card_le_card subset

/-- GreedyASS's leaf-oriented lazy-finger bound, for the executable sweep
from an empty history. Its additive startup allowance is fifteen per leaf. -/
theorem cost (t : Tree) (lo : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t) :
    rowCost greedySweep 0 ∅ xs ≤ 24 * referenceCost t lo xs + 15 * leaves t := by
  have bound := stream t lo xs valid
  have columns := columns_bound t lo xs valid
  rw [points_card (lo + leaves t) xs (fun x hx => (valid x hx).2)] at bound
  omega

end RotationBST.Geometric.GreedyASS.Potential.Amortized
