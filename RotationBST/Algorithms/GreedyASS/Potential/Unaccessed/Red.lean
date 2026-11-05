module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.External
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- An unaccessed red point keeps its color and selected value, even if
it changes from glancing to internal. The reference history is fixed. -/
theorem red_value (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {q : Point} (active : Active P q) (colored : color t lo searches P q = some .red)
    (untouched : q.1 ∉ keys) :
    color t lo searches (P ∪ row time keys) q = some .red ∧
      value t lo searches (P ∪ row time keys) q = value t lo searches P q := by
  have nonexternal : ¬ External P q := by
    intro external
    rw [(external_spec t lo searches external).1] at colored
    split at colored
    · contradiction
    · split at colored <;> contradiction
  have newActive := (active_unchanged P time keys q untouched).mpr active
  have newNonexternal : ¬ External (P ∪ row time keys) q :=
    fun ext => nonexternal ((external_unchanged keys history active untouched).mp ext)
  by_cases glancing : Glancing (P ∪ row time keys) q
  · have oldGlancing : Glancing P q := by
      rcases glancing with left | right
      · exact Or.inl ((left_glancing_update keys history active untouched).mp left).1
      · exact Or.inr ((right_glancing_update keys history active untouched).mp right).1
    obtain ⟨sameColor, sameValue⟩ := glancing_unchanged t lo searches keys history oldGlancing glancing
    exact ⟨sameColor.trans colored, sameValue⟩
  · obtain ⟨newColor, newValue⟩ := internal_spec t lo searches ⟨newActive, newNonexternal, glancing⟩
    refine ⟨newColor, ?_⟩
    rw [newValue, red_unchanged t lo keys history active.1]
    simp only [value, colored]

/-- Item-level red stability, including the actual latest-point query and
natural-valued amount. No ASS hypothesis is needed for this case. -/
theorem red_amount (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {x : Nat} (colored : itemColor t lo searches P x = some .red) (untouched : x ∉ keys) :
    itemColor t lo searches (P ∪ row time keys) x = some .red ∧
      itemAmount t lo searches (P ∪ row time keys) x = itemAmount t lo searches P x := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at colored
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have oldColor : color t lo searches P (x, stamp) = some .red := by
      simpa only [itemColor, recent] using colored
    obtain ⟨newColor, sameValue⟩ := red_value t lo searches keys history active oldColor untouched
    have newActive := (active_unchanged P time keys (x, stamp) untouched).mpr active
    have oldItem := (item_spec t lo searches active).2
    have newItem := (item_spec t lo searches newActive).2
    refine ⟨(item_spec t lo searches newActive).1.trans newColor, ?_⟩
    have equal := newItem.trans (sameValue.trans oldItem.symm)
    rw [Accessed.amount_exact, Accessed.amount_exact] at equal
    exact WithTop.coe_inj.mp equal

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
