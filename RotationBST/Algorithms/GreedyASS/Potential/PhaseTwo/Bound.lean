module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.Counting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
open Items Reference

/-- The complete Phase-II amortized bound, combining all items and virgin
roots. Only the explicit allowance for first accesses survives. -/
theorem bound (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t)
    (domain : Finset Nat) (covers : Virgin.keys searches searched ⊆ domain) :
    (Virgin.keys searches searched).card +
        totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) domain +
        Virgin.after t lo searches searched ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) domain +
        Virgin.before t lo searches searched + 24 +
        3 * (unseenKeys (Virgin.points searches) (Virgin.keys searches searched)).card := by
  have itemBound := items t lo searches searched valid domain covers
  have counts := color_counts t lo searches searched valid
  have virgin := Virgin.decrease t lo searches searched valid
  dsimp only at itemBound
  omega

/-- The canonical whole-universe instance needs only valid search ranks.
Both sides use the current reference history; Phase I is separate. -/
theorem step (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.keys searches searched).card +
        totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) (Finset.range (lo + leaves t)) +
        Virgin.after t lo searches searched ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) (Finset.range (lo + leaves t)) +
        Virgin.before t lo searches searched + 24 +
        3 * (unseenKeys (Virgin.points searches) (Virgin.keys searches searched)).card := by
  apply bound t lo searches searched valid
  intro x hx
  have point : (x, searches.length) ∈ Virgin.points (searches ++ [searched]) := by
    rw [Virgin.points_snoc]
    exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩)
  exact Finset.mem_range.mpr (Unaccessed.points_property _ (searches ++ [searched]) valid _ point).2

end RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
