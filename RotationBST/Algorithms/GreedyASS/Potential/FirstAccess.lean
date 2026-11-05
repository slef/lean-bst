module

public import RotationBST.Algorithms.GreedyASS.Potential.Rows
public import RotationBST.Algorithms.GreedyASS.Abstract
public import RotationBST.Models.Geometric.Online.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

theorem latest_none (P : Finset Point) (x : Nat) : latest P x = none ↔ x ∉ P.image Prod.fst := by
  rw [latest, greatest_none]
  constructor
  · intro empty member
    obtain ⟨q, hq, coord⟩ := Finset.mem_image.mp member
    have member : q.2 ∈ times P x :=
      (mem_times P x q.2).mpr (by simpa only [← coord] using hq)
    simp only [empty, Finset.notMem_empty] at member
  · intro unseen
    apply Finset.eq_empty_of_forall_notMem
    intro stamp member
    exact unseen (Finset.mem_image.mpr ⟨(x, stamp), (mem_times P x stamp).mp member, rfl⟩)

theorem unseen_eq (P : Finset Point) (keys : Finset Nat) : unseenKeys P keys = keys \ P.image Prod.fst := by
  ext x
  simp [unseenKeys, latest_none]

theorem columns_step (P : Finset Point) (time : Nat) (keys : Finset Nat) :
    ((P ∪ row time keys).image Prod.fst).card = (P.image Prod.fst).card + (unseenKeys P keys).card := by
  have columns : (P ∪ row time keys).image Prod.fst = P.image Prod.fst ∪ keys := by
    ext x
    simp only [Finset.mem_image, Finset.mem_union, mem_row]
    aesop
  rw [columns, unseen_eq]
  have union := Finset.card_union_add_card_inter (P.image Prod.fst) keys
  have difference := Finset.card_sdiff_add_card_inter keys (P.image Prod.fst)
  rw [Finset.inter_comm keys] at difference
  omega

/-- First-access charges telescope exactly into the number of new columns. -/
theorem first_access_exact (time : Nat) (P : Finset Point) (xs : List Nat) :
    (P.image Prod.fst).card + firstAccesses time P xs =
      ((fill greedySweep time P xs).image Prod.fst).card := by
  induction xs generalizing time P with
  | nil => simp [firstAccesses, fill]
  | cons x xs ih =>
    have step := columns_step P time (greedySweep time x P)
    have rest := ih (time + 1) (P ∪ row time (greedySweep time x P))
    simp only [firstAccesses, fill]
    omega

/-- Even on arbitrarily long streams, unseen-row charges are paid at most
once per universe key, after crediting columns already in the history. -/
theorem first_access_bound {n time : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n time P) (satisfied : ASS P) (valid : ∀ x ∈ xs, x < n) :
    (P.image Prod.fst).card + firstAccesses time P xs ≤ n := by
  have finalHistory := (fill_spec (greedyASS n) time P xs history satisfied valid).2.1
  rw [first_access_exact]
  have subset : (fill greedySweep time P xs).image Prod.fst ⊆ Finset.range n := by
    intro x member
    obtain ⟨q, hq, coord⟩ := Finset.mem_image.mp member
    exact Finset.mem_range.mpr (coord ▸ (finalHistory q hq).1)
  simpa only [Finset.card_range] using Finset.card_le_card subset

end RotationBST.Geometric.GreedyASS.Potential
