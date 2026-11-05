module

public import RotationBST.Algorithms.GreedyASS.Potential.Rows
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

/-- Every newly accessed item has potential at most its current blue value.
If it becomes red, its potential is strictly smaller than that value. -/
theorem top_bound (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        WithTop.some (blue t lo searched x) ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          WithTop.some (blue t lo searched x)) := by
  obtain ⟨hc, hv⟩ := item_spec t lo (searches ++ [searched]) (top_active keys history member)
  rw [hc, hv]
  rcases (top_classification keys history member).1 with external | glancing
  · obtain ⟨colored, valued⟩ := external_spec t lo (searches ++ [searched]) external
    have latest := top_latest keys history
    simp only [latest, ↓reduceIte, currentBlue, List.getLast?_append,
      List.getLast?_singleton] at colored valued
    rw [colored, valued]
    simp
  · obtain ⟨colored, valued⟩ := glancing_spec t lo (searches ++ [searched]) glancing
    rw [purple_reset] at colored valued
    rw [valued]
    refine ⟨min_le_right _ _, ?_⟩
    intro isRed
    by_cases smaller : red t lo (P ∪ row searches.length keys) (x, searches.length) <
        WithTop.some (blue t lo searched x)
    · exact lt_of_le_of_lt (min_le_left _ _) smaller
    · simp only [smaller, ↓reduceIte] at colored
      rw [colored] at isRed
      contradiction

/-- New accesses cannot be green, including the top-corner exception. -/
theorem top_not_green (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys) :
    itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≠ some .green := by
  rw [(item_spec t lo (searches ++ [searched]) (top_active keys history member)).1]
  rcases (top_classification keys history member).1 with external | glancing
  · rw [(external_spec t lo (searches ++ [searched]) external).1]
    simp [top_latest keys history]
  · rw [(glancing_spec t lo (searches ++ [searched]) glancing).1]
    split <;> simp

/-- Lemma 3.11, including strict decrease when the new color is red. -/
theorem blue_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys)
    (old : itemColor t lo (searches ++ [searched]) P x = some .blue) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          itemValue t lo (searches ++ [searched]) P x) := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at old
  | some stamp =>
    have colored : color t lo (searches ++ [searched]) P (x, stamp) = some .blue := by
      simpa only [itemColor, recent] using old
    have valued : itemValue t lo (searches ++ [searched]) P x = WithTop.some (blue t lo searched x) := by
      simp [itemValue, recent, value, colored, currentBlue]
    rw [valued]
    exact top_bound t lo searches searched keys history member

/-- Lemma 3.10. The old purple maximum includes the current blue value,
whereas a fresh access resets that maximum to the current value. -/
theorem purple_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys)
    (old : itemColor t lo (searches ++ [searched]) P x = some .purple) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          itemValue t lo (searches ++ [searched]) P x) := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at old
  | some stamp =>
    have colored : color t lo (searches ++ [searched]) P (x, stamp) = some .purple := by
      simpa only [itemColor, recent] using old
    have valued : itemValue t lo (searches ++ [searched]) P x =
        WithTop.some (purple t lo (searches ++ [searched]) stamp x) := by
      simp [itemValue, recent, value, colored]
    have age := (history (x, stamp) ((latest_spec P x stamp).mp recent).1).2
    have bound : WithTop.some (blue t lo searched x) ≤
        WithTop.some (purple t lo (searches ++ [searched]) stamp x) :=
      WithTop.coe_le_coe.mpr (purple_ge_blue t lo searches searched stamp x (Nat.le_of_lt age))
    obtain ⟨weak, strict⟩ := top_bound t lo searches searched keys history member
    rw [valued]
    exact ⟨weak.trans bound, fun red => (strict red).trans_le bound⟩

end RotationBST.Geometric.GreedyASS.Potential.Accessed
