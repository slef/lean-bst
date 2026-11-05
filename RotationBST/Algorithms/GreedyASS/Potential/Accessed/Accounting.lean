module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Visibility
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

theorem amount_exact (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) :
    itemValue t lo searches P x = WithTop.some (itemAmount t lo searches P x) := by
  have existsValue : ∃ v : Nat, itemValue t lo searches P x = WithTop.some v := by
    cases recent : latest P x with
    | none => exact ⟨0, by simp [itemValue, recent]⟩
    | some stamp =>
      obtain ⟨v, value⟩ := finite t lo searches P (x, stamp)
      exact ⟨v, by simpa only [itemValue, recent] using value⟩
  obtain ⟨v, value⟩ := existsValue
  simp only [itemAmount, value]
  rfl

/-- The three old non-green color cases, with the unit loss of every new
red item expressed in natural arithmetic rather than truncated subtraction. -/
theorem unit_credit (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .red ∨
      itemColor t lo (searches ++ [searched]) P x = some .blue ∨
      itemColor t lo (searches ++ [searched]) P x = some .purple) :
    itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x +
      (if itemColor t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red then 1 else 0) ≤
      itemAmount t lo (searches ++ [searched]) P x := by
  have bounds :
      itemValue t lo (searches ++ [searched])
          (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched])
          (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red →
        itemValue t lo (searches ++ [searched])
          (P ∪ row searches.length (greedySweep searches.length searched P)) x <
        itemValue t lo (searches ++ [searched]) P x) := by
    rcases old with red | blue | purple
    · exact red_access t lo searches searched history valid member red
    · exact blue_access t lo searches searched _ history member blue
    · exact purple_access t lo searches searched _ history member purple
  rw [amount_exact t lo (searches ++ [searched]) P x,
    amount_exact t lo (searches ++ [searched]) _ x] at bounds
  simp only [WithTop.coe_le_coe, WithTop.coe_lt_coe] at bounds
  split
  · have := bounds.2 (by assumption)
    omega
  · have := bounds.1
    omega

/-- Summing actual item potentials pays for every new red access among
items that were red, blue, or purple at the intermediate snapshot. Green
and unseen items are deliberately left for their separate inequalities. -/
theorem total_credit (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (keys : Finset Nat)
    (accessed : keys ⊆ greedySweep searches.length searched P)
    (old : ∀ x ∈ keys, itemColor t lo (searches ++ [searched]) P x = some .red ∨
      itemColor t lo (searches ++ [searched]) P x = some .blue ∨
      itemColor t lo (searches ++ [searched]) P x = some .purple) :
    totalAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) keys +
      (coloredKeys t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) keys .red).card ≤
      totalAmount t lo (searches ++ [searched]) P keys := by
  have bound := Finset.sum_le_sum (fun x hx =>
    unit_credit t lo searches searched history valid (accessed hx) (old x hx))
  simpa only [Finset.sum_add_distrib, totalAmount, coloredKeys, Finset.card_filter] using bound

end RotationBST.Geometric.GreedyASS.Potential.Accessed
