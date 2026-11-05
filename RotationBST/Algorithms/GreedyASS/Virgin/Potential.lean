module

public import RotationBST.Algorithms.GreedyASS.Virgin.Counting
public import RotationBST.Algorithms.GreedyASS.Virgin.Lifetime
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

/-- The touched row splits exactly into old and virgin components. -/
theorem touched_partition (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    (touched t lo history request).card = (oldTouched t lo history request).card +
      (roots t lo history request ∩ touched t lo history request).card := by
  classical
  have complement : touched t lo history request \ oldTouched t lo history request =
      roots t lo history request ∩ touched t lo history request := by
    ext c
    simp only [oldTouched, roots, touched, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_inter, List.mem_toFinset]
    aesop
  have subset : oldTouched t lo history request ⊆ touched t lo history request :=
    Finset.filter_subset _ _
  have split := Finset.card_sdiff_add_card_eq_card subset
  rw [complement] at split
  omega

/-- Exact Phase-II virgin-potential decrease, with no subtraction of signed
potential changes hidden in natural-number arithmetic. -/
theorem exact_drop (t : Tree) (lo : Nat) (history : List Nat) (request : Nat) :
    before t lo history request = after t lo history request +
      12 * (roots t lo history request ∩ touched t lo history request).card := by
  have split := Finset.card_sdiff_add_card_inter
    (roots t lo history request) (touched t lo history request)
  unfold before after
  omega

/-- Lemma 3.8 in an additive form valid even when fewer than two roots are
touched: the loss is at least twelve times the touched count minus 24. -/
theorem decrease (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t) :
    after t lo history request + 12 * (touched t lo history request).card ≤
      before t lo history request + 24 := by
  have old := count t lo history request valid
  have split := touched_partition t lo history request
  have drop := exact_drop t lo history request
  omega

end RotationBST.Geometric.GreedyASS.Virgin
