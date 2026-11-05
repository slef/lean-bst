module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Accounting
public import RotationBST.Algorithms.GreedyASS.Potential.FirstAccess
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

theorem blue_searched (t : Tree) (lo x : Nat) : blue t lo x x = 2 := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    by_cases side : x < lo + leaves l <;> simp [blue, side, il, ir]

/-- A projected access already has an old point. Thus only the requested
key can be a first access in the current sweep. -/
theorem unseen_searched {P : Finset Point} {time searched x : Nat}
    (member : x ∈ greedySweep time searched P) (unseen : latest P x = none) : x = searched := by
  rcases Finset.mem_insert.mp member with same | projected
  · exact same
  · obtain ⟨q, hq, eq⟩ := Finset.mem_image.mp projected
    exact ((latest_none P x).mp unseen
      (Finset.mem_image.mpr ⟨q, (Finset.mem_filter.mp hq).1, eq⟩)).elim

/-- A first access costs at most two units of new item potential, in
addition to its one unit of actual access cost. -/
theorem unseen_amount (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P) (unseen : latest P x = none) :
    itemAmount t lo (searches ++ [searched]) P x = 0 ∧
      itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤ 2 := by
  have same := unseen_searched member unseen
  subst x
  constructor
  · simp only [itemAmount, itemValue, unseen]
    rfl
  · have bound := (top_bound t lo searches searched _ history member).1
    rw [blue_searched, amount_exact] at bound
    exact WithTop.coe_le_coe.mp bound

theorem unseen_total (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P) :
    totalAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P))
        (unseenKeys P (greedySweep searches.length searched P)) +
      (unseenKeys P (greedySweep searches.length searched P)).card ≤
      3 * (unseenKeys P (greedySweep searches.length searched P)).card := by
  have each : ∀ x ∈ unseenKeys P (greedySweep searches.length searched P),
      itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤ 2 := by
    intro x hx
    obtain ⟨member, unseen⟩ := Finset.mem_filter.mp hx
    exact (unseen_amount t lo searches searched history member unseen).2
  have bound := Finset.sum_le_sum each
  simp only [Finset.sum_const, smul_eq_mul] at bound
  unfold totalAmount
  omega

end RotationBST.Geometric.GreedyASS.Potential.Accessed
