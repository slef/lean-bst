module

public import RotationBST.Algorithms.Combination.Rounds.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Rounds

/-- Ordered disjoint spans cannot charge any request more than once. -/
theorem disjoint_charge (weights : Nat → ℝ) (nonneg : ∀ i, 0 ≤ weights i)
    (rounds : List Span) (lo hi : Nat) (ordered : rounds.Pairwise fun a b => a.stop ≤ b.start)
    (inside : ∀ span ∈ rounds, lo ≤ span.start ∧ span.start ≤ span.stop ∧ span.stop ≤ hi) :
    (rounds.map (Span.charge weights)).sum ≤ ∑ i ∈ Finset.Ico lo hi, weights i := by
  induction rounds generalizing lo with
  | nil => exact Finset.sum_nonneg fun i _ => nonneg i
  | cons span rest ih =>
    have head := inside span (List.mem_cons_self ..)
    have order := List.pairwise_cons.mp ordered
    have tail := ih span.stop order.2 (by
      intro later member
      exact ⟨order.1 later member, (inside later (List.mem_cons_of_mem _ member)).2⟩)
    simp only [List.map_cons, List.sum_cons]
    calc
      Span.charge weights span + (rest.map (Span.charge weights)).sum ≤
          Span.charge weights span + ∑ i ∈ Finset.Ico span.stop hi, weights i := add_le_add le_rfl tail
      _ = ∑ i ∈ Finset.Ico span.start hi, weights i := Finset.sum_Ico_consecutive weights head.2.1 head.2.2
      _ ≤ ∑ i ∈ Finset.Ico lo hi, weights i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i member
          have bounds := Finset.mem_Ico.mp member
          exact Finset.mem_Ico.mpr ⟨by omega, bounds.2⟩
        · intro i _ _
          exact nonneg i

/-- Selecting either worker turns same-worker separation into an ordered
list of disjoint intervals. -/
theorem selected_separated (selected : Bool) (rounds : List Span) (separated : Separated rounds) :
    (rounds.filter fun span => span.side == selected).Pairwise fun a b => a.stop ≤ b.start := by
  apply List.pairwise_filter.mpr
  apply separated.imp
  intro a b relation ha hb
  have aSide : a.side = selected := by simpa only [beq_iff_eq] using ha
  have bSide : b.side = selected := by simpa only [beq_iff_eq] using hb
  exact relation (aSide.trans bSide.symm)

/-- The selected worker's round charges are bounded by the original charges
on the entire input interval. No request is double-counted at interruptions. -/
theorem charge_le_interval {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (selected : Bool)
    (weights : Nat → ℝ) (nonneg : ∀ i, 0 ≤ weights i) :
    charge selected weights (spans worker budget restore s offset xs) ≤
      ∑ i ∈ Finset.Ico offset (offset + xs.length), weights i := by
  apply disjoint_charge weights nonneg _ offset (offset + xs.length)
    (selected_separated selected _ (spans_separated worker budget restore s offset xs))
  intro span member
  exact spans_bounds worker budget restore s offset xs span (List.mem_of_mem_filter member)

end RotationBST.Combo.Rounds
