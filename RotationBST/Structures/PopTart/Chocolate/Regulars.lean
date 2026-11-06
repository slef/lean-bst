module

public import RotationBST.Structures.PopTart.Chocolate.Invariant
public import RotationBST.Structures.PopTart.Height
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Nonnegative regular crumbs only increase the mass of the suffix. -/
theorem attach_mass {rs : Regulars} {level : Nat} (valid : rs.Valid level) (tail : WeightedTree) :
    tail.mass ≤ (rs.attach tail).mass := by
  cases rs with
  | zero => exact le_rfl
  | one a =>
    have ha := mass_nonnegative valid.2
    change tail.mass ≤ a.mass + tail.mass
    linarith only [ha]
  | two a b =>
    have ha := mass_nonnegative valid.1.2
    have hb := mass_nonnegative valid.2.2
    change tail.mass ≤ a.mass + (b.mass + tail.mass)
    linarith only [ha, hb]
  | three a b c =>
    have ha := mass_nonnegative valid.1.2
    have hb := mass_nonnegative valid.2.1.2
    have hc := mass_nonnegative valid.2.2.2
    change tail.mass ≤ a.mass + (b.mass + (c.mass + tail.mass))
    linarith only [ha, hb, hc]

/-- A slot lies in a perfect regular crumb or crosses at most three regular
nodes before reaching the suffix. -/
theorem attach_slot {rs : Regulars} {level : Nat} (valid : rs.Valid level)
    {tail : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (rs.attach tail) subtree weight depth) :
    depth ≤ level + 3 ∨ ∃ d, SlotAt tail subtree weight d ∧ depth ≤ d + 3 := by
  cases rs with
  | zero => exact Or.inr ⟨depth, slot, by omega⟩
  | one a =>
    cases slot with
    | left found => have eq := perfect_depth valid.1 found; exact Or.inl (by omega)
    | right found => exact Or.inr ⟨_, found, by omega⟩
  | two a b =>
    cases slot with
    | left found => have eq := perfect_depth valid.1.1 found; exact Or.inl (by omega)
    | right found =>
      cases found with
      | left hit => have eq := perfect_depth valid.2.1 hit; exact Or.inl (by omega)
      | right hit => exact Or.inr ⟨_, hit, by omega⟩
  | three a b c =>
    cases slot with
    | left found => have eq := perfect_depth valid.1.1 found; exact Or.inl (by omega)
    | right found =>
      cases found with
      | left hit => have eq := perfect_depth valid.2.1.1 hit; exact Or.inl (by omega)
      | right hit =>
        cases hit with
        | left last => have eq := perfect_depth valid.2.2.1 last; exact Or.inl (by omega)
        | right last => exact Or.inr ⟨_, last, by omega⟩

end RotationBST.PopTart.Chocolate
