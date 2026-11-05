module

public import RotationBST.Algorithms.GreedyASS.Potential.Colors
public import RotationBST.Algorithms.GreedyASS.Items.TopRow
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

theorem active_color (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (active : Active P q) : ∃ c, color t lo searches P q = some c := by
  simp only [color, active, not_true_eq_false, ↓reduceIte]
  split_ifs <;> simp

theorem item_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {x stamp : Nat}
    (active : Active P (x, stamp)) :
    itemColor t lo searches P x = color t lo searches P (x, stamp) ∧
      itemValue t lo searches P x = value t lo searches P (x, stamp) := by
  have recent := (latest_spec P x stamp).mpr active
  simp [itemColor, itemValue, recent]

theorem item_none (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) :
    itemColor t lo searches P x = none ↔ latest P x = none := by
  cases recent : latest P x with
  | none => simp [itemColor, recent]
  | some stamp =>
    obtain ⟨c, colored⟩ := active_color t lo searches ((latest_spec P x stamp).mp recent)
    simp [itemColor, recent, colored]

/-- Intermediate rows may contain never-accessed keys. Keep their count
explicit instead of silently assigning them an old color. -/
theorem partition (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (keys : Finset Nat) :
    keys.card = (unseenKeys P keys).card +
      (coloredKeys t lo searches P keys .red).card + (coloredKeys t lo searches P keys .green).card +
      (coloredKeys t lo searches P keys .blue).card + (coloredKeys t lo searches P keys .purple).card := by
  have enumeration : ∀ x ∈ keys, itemColor t lo searches P x ∈
      ({none, some .red, some .green, some .blue, some .purple} : Finset (Option Color)) := by
    intro x _
    cases itemColor t lo searches P x with
    | none => simp
    | some c => cases c <;> simp
  have counts := Finset.card_eq_sum_card_fiberwise enumeration
  simpa [coloredKeys, unseenKeys, item_none, Nat.add_assoc] using counts

theorem row_partition (t : Tree) (lo : Nat) (searches : List Nat) {n time : Nat}
    {P : Finset Point} (keys : Finset Nat) (history : History n time P) :
    keys.card =
      (coloredKeys t lo searches (P ∪ row time keys) keys .red).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .green).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .blue).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .purple).card := by
  have unseen : unseenKeys (P ∪ row time keys) keys = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x member
    have recent := (latest_spec (P ∪ row time keys) x time).mpr (top_active keys history member)
    simp only [recent, reduceCtorEq, not_false_eq_true]
  have counts := partition t lo searches (P ∪ row time keys) keys
  simpa only [unseen, Finset.card_empty, Nat.zero_add] using counts

end RotationBST.Geometric.GreedyASS.Potential
