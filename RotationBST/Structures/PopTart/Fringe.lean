module

public import RotationBST.Structures.PopTart.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

theorem fringe_length (t : WeightedTree) : t.fringe.length = t.leafCount := by
  induction t <;> simp_all [fringe, leafCount]

theorem fringe_mass (t : WeightedTree) : (t.fringe.map Prod.snd).sum = t.mass := by
  induction t <;> simp_all [fringe, mass]

theorem fringe_nonnegative (t : WeightedTree) :
    t.Nonnegative ↔ ∀ p ∈ t.fringe, 0 ≤ p.2 := by
  induction t <;> simp_all [Nonnegative, fringe]
  aesop

/-- Every slot occurrence has its own exact prefix and suffix in the fringe. -/
theorem slot_split {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) :
    ∃ before after, t.fringe = before ++ (subtree, weight) :: after := by
  induction slot with
  | leaf => exact ⟨[], [], rfl⟩
  | @left l r subtree weight depth found ih =>
    obtain ⟨before, after, split⟩ := ih
    exact ⟨before, after ++ r.fringe, by simp [fringe, split, List.append_assoc]⟩
  | @right l r subtree weight depth found ih =>
    obtain ⟨before, after, split⟩ := ih
    exact ⟨l.fringe ++ before, after, by simp [fringe, split, List.append_assoc]⟩

theorem ordered_append {t a b : WeightedTree} (split : t.fringe = a.fringe ++ b.fringe) :
    t.Ordered ↔ a.Ordered ∧ b.Ordered ∧
      ∀ x ∈ a.fringe, ∀ y ∈ b.fringe, y.2 ≤ x.2 := by
  simp only [Ordered, fringe_nonnegative, split, List.mem_append, List.pairwise_append]
  aesop

/-- An ordered prefix ending at weight `w` contributes at least its length
 times `w`, even when later occurrences have weight zero. -/
theorem ordered_prefix_mass {t : WeightedTree} (ordered : t.Ordered)
    {before after : List (Tree × ℝ)} {subtree : Tree} {weight : ℝ}
    (split : t.fringe = before ++ (subtree, weight) :: after) :
    ((before.length + 1 : Nat) : ℝ) * weight ≤ t.mass := by
  have pairwise := ordered.2
  rw [split, List.pairwise_append] at pairwise
  have lower : (before.length : ℝ) * weight ≤ (before.map Prod.snd).sum := by
    have each : ∀ p ∈ before, weight ≤ p.2 := by
      intro p mem
      exact pairwise.2.2 p mem (subtree, weight) (by simp)
    clear split pairwise
    induction before with
    | nil => simp
    | cons p ps ih =>
      have hp := each p (by simp)
      have hs := ih (by intro q hq; exact each q (by simp [hq]))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons]
      nlinarith only [hp, hs]
  have nonnegative := (fringe_nonnegative t).mp ordered.1
  have afterNonnegative : 0 ≤ (after.map Prod.snd).sum := by
    apply List.sum_nonneg
    intro value mem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp mem
    exact nonnegative p (by rw [split]; simp [hp])
  have total := fringe_mass t
  rw [split] at total
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at total
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [lower, afterNonnegative, total]

end RotationBST.PopTart.WeightedTree
