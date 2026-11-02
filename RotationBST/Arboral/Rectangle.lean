module

public import RotationBST.Arboral.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Set.Finite.Lemmas

import Mathlib.Tactic.Push

@[expose] public section
namespace RotationBST.Arboral

theorem rectangle_trans {a b p q : Point} (hp : Rectangle a b p)
    (hq : Rectangle a p q) : Rectangle a b q := by
  unfold Rectangle at *
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨h5, h6, h7, h8⟩ := hq
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

private def distance (a b : Point) : Nat :=
  Nat.dist a.1 b.1 + Nat.dist a.2 b.2

private theorem distance_lt {a b p : Point} (h : Rectangle a b p) (hne : p ≠ b) :
    distance a p < distance a b := by
  have ne : p.1 ≠ b.1 ∨ p.2 ≠ b.2 := by
    by_contra hn
    push Not at hn
    exact hne (Prod.ext hn.1 hn.2)
  unfold distance Nat.dist Rectangle at *
  obtain ⟨h1, h2, h3, h4⟩ := h
  omega

/-- Satisfaction forces a witness on a side incident to either chosen corner,
not merely somewhere in the rectangle. -/
theorem side_witness {P : Finset Point} (sat : ASS P)
    {a b : Point} (ha : a ∈ P) (hb : b ∈ P) (hx : a.1 ≠ b.1) (hy : a.2 ≠ b.2) :
    ∃ p ∈ P, p ≠ a ∧ p ≠ b ∧ Rectangle a b p ∧ (p.1 = a.1 ∨ p.2 = a.2) := by
  classical
  let S := P.filter fun p => p ≠ a ∧ Rectangle a b p
  have bmem : b ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_, ?_⟩
    · intro h; exact hx (congrArg Prod.fst h.symm)
    · exact ⟨min_le_right _ _, le_max_right _ _, min_le_right _ _, le_max_right _ _⟩
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image (distance a) ⟨b, bmem⟩
  obtain ⟨hpP, hpa, hrect⟩ := Finset.mem_filter.mp hp
  have side : p.1 = a.1 ∨ p.2 = a.2 := by
    by_contra hn
    push Not at hn
    obtain ⟨q, hq, hqa, hqp, hqr⟩ := sat a ha p hpP (Ne.symm hn.1) (Ne.symm hn.2)
    have hqS : q ∈ S := Finset.mem_filter.mpr
      ⟨hq, hqa, rectangle_trans hrect hqr⟩
    have := hmin q hqS
    have := distance_lt hqr hqp
    omega
  refine ⟨p, hpP, hpa, ?_, hrect, side⟩
  intro heq
  subst p
  rcases side with h | h
  · exact hx h.symm
  · exact hy h.symm

end RotationBST.Arboral
