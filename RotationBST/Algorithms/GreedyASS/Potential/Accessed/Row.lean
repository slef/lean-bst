module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.ExactNeighbors
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Startup
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

/-- All four old colors pay for a newly red access. An unseen column has
an explicit startup allowance instead of a fictitious old color. -/
theorem all_credit (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P) :
    itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x +
      (if itemColor t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red then 1 else 0) ≤
      itemAmount t lo (searches ++ [searched]) P x + 3 * (if latest P x = none then 1 else 0) := by
  by_cases unseen : latest P x = none
  · obtain ⟨before, after⟩ := unseen_amount t lo searches searched history member unseen
    rw [before, ite_eq_left unseen]
    split <;> omega
  · rw [ite_eq_right unseen, Nat.mul_zero, Nat.add_zero]
    cases colored : itemColor t lo (searches ++ [searched]) P x with
    | none => exact (unseen ((item_none t lo _ P x).mp colored)).elim
    | some c =>
      cases c with
      | red => exact unit_credit t lo searches searched history valid member (Or.inl colored)
      | blue => exact unit_credit t lo searches searched history valid member (Or.inr (Or.inl colored))
      | purple => exact unit_credit t lo searches searched history valid member (Or.inr (Or.inr colored))
      | green =>
        have bound := green_access t lo searches searched satisfied history valid member colored
        split <;> omega

/-- The full accessed-row bound. The sum includes every actual access,
all old colors, and first accesses. Only the new blue/purple counts and an
explicit startup term remain on the right-hand side. -/
theorem row_bound (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) :
    let keys := greedySweep searches.length searched P
    let Q := P ∪ row searches.length keys
    keys.card + totalAmount t lo (searches ++ [searched]) Q keys ≤
      totalAmount t lo (searches ++ [searched]) P keys +
        (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
        (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
        3 * (unseenKeys P keys).card := by
  dsimp only
  let keys := greedySweep searches.length searched P
  let Q := P ∪ row searches.length keys
  have summed := Finset.sum_le_sum (fun x hx => all_credit t lo searches searched satisfied history valid hx)
  have bound : totalAmount t lo (searches ++ [searched]) Q keys +
      (coloredKeys t lo (searches ++ [searched]) Q keys .red).card ≤
      totalAmount t lo (searches ++ [searched]) P keys + 3 * (unseenKeys P keys).card := by
    simpa only [totalAmount, coloredKeys, unseenKeys, Finset.card_filter,
      Finset.sum_add_distrib, Finset.mul_sum] using summed
  have noGreen : coloredKeys t lo (searches ++ [searched]) Q keys .green = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro x member
    exact top_not_green t lo searches searched keys history member
  have counts := row_partition t lo (searches ++ [searched]) keys history
  change keys.card = (coloredKeys t lo (searches ++ [searched]) Q keys .red).card +
    (coloredKeys t lo (searches ++ [searched]) Q keys .green).card +
    (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
    (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card at counts
  rw [noGreen, Finset.card_empty] at counts
  change keys.card + totalAmount t lo (searches ++ [searched]) Q keys ≤
    totalAmount t lo (searches ++ [searched]) P keys +
      (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
      (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
      3 * (unseenKeys P keys).card
  omega

end RotationBST.Geometric.GreedyASS.Potential.Accessed
