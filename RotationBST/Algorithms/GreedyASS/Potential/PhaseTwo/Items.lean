module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.All
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Row
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
open Items Reference

/-- Sum accessed and unaccessed contributions over any finite domain
containing the new row. The three-unit startup allowance is explicit. -/
theorem items (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    (valid : ∀ x ∈ searches ++ [searched], lo ≤ x ∧ x < lo + leaves t)
    (domain : Finset Nat) (covers : Virgin.keys searches searched ⊆ domain) :
    let keys := Virgin.keys searches searched
    let Q := Virgin.points (searches ++ [searched])
    keys.card + totalAmount t lo (searches ++ [searched]) Q domain ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) domain +
        (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
        (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
        3 * (unseenKeys (Virgin.points searches) keys).card := by
  let keys := Virgin.keys searches searched
  let P := Virgin.points searches
  let Q := Virgin.points (searches ++ [searched])
  have oldValid : ∀ x ∈ searches, x < lo + leaves t :=
    fun x hx => (valid x (List.mem_append_left _ hx)).2
  have pointValid : ∀ p ∈ P, lo ≤ p.1 ∧ p.1 < lo + leaves t :=
    Unaccessed.points_property _ searches (fun x hx => valid x (List.mem_append_left _ hx))
  have accessed := Accessed.row_bound t lo searches searched
    (Unaccessed.points_satisfied searches oldValid)
    (Virgin.points_history _ searches oldValid) pointValid
  change keys.card + totalAmount t lo (searches ++ [searched])
    (P ∪ row searches.length keys) keys ≤
      totalAmount t lo (searches ++ [searched]) P keys +
        (coloredKeys t lo (searches ++ [searched]) (P ∪ row searches.length keys) keys .blue).card +
        (coloredKeys t lo (searches ++ [searched]) (P ∪ row searches.length keys) keys .purple).card +
        3 * (unseenKeys P keys).card at accessed
  have next : P ∪ row searches.length keys = Q := (Virgin.points_snoc searches searched).symm
  rw [next] at accessed
  have untouched := Unaccessed.all_total t lo searches searched (fun x hx => (valid x hx).2)
    (domain \ keys) (fun x hx => (Finset.mem_sdiff.mp hx).2)
  have oldSum := Finset.sum_sdiff (f := itemAmount t lo (searches ++ [searched]) P) covers
  have newSum := Finset.sum_sdiff (f := itemAmount t lo (searches ++ [searched]) Q) covers
  change totalAmount t lo (searches ++ [searched]) P (domain \ keys) +
    totalAmount t lo (searches ++ [searched]) P keys = totalAmount t lo (searches ++ [searched]) P domain at oldSum
  change totalAmount t lo (searches ++ [searched]) Q (domain \ keys) +
    totalAmount t lo (searches ++ [searched]) Q keys = totalAmount t lo (searches ++ [searched]) Q domain at newSum
  change totalAmount t lo (searches ++ [searched]) Q (domain \ keys) ≤
    totalAmount t lo (searches ++ [searched]) P (domain \ keys) at untouched
  change keys.card + totalAmount t lo (searches ++ [searched]) Q domain ≤
    totalAmount t lo (searches ++ [searched]) P domain +
      (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
      (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
      3 * (unseenKeys P keys).card
  omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseTwo
