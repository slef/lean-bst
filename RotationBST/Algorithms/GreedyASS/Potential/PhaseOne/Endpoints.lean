module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Values
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- At the initial forest, the old historical maximum already contains
current blue, so introducing the frozen-floor representation changes nothing. -/
theorem select_current (t : Tree) (lo : Nat) (prior : List Nat) (old : Nat)
    {n : Nat} {P : Finset Point} (history : History n (prior.length + 1) P) (q : Point) :
    select t lo (prior ++ [old]) P q (blue t lo old q.1) = value t lo (prior ++ [old]) P q := by
  by_cases active : Active P q
  · have age : q.2 ≤ prior.length := by have := (history q active.1).2; omega
    have floor := purple_ge_blue t lo prior old q.2 q.1 age
    by_cases external : External P q
    · rw [(external_spec t lo (prior ++ [old]) external).2]
      simp only [select, active, not_true_eq_false, ite_false, external, ite_true,
        currentBlue, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    · by_cases glancing : Glancing P q
      · rw [(glancing_spec t lo (prior ++ [old]) glancing).2]
        simp only [select, active, not_true_eq_false, ite_false, external, glancing,
          ite_true, max_eq_left floor]
      · rw [(internal_spec t lo (prior ++ [old]) ⟨active, external, glancing⟩).2]
        simp only [select, active, not_true_eq_false, ite_false, external, glancing]
  · simp [select, value, color, active]

/-- At the final forest, taking the max with its blue value is exactly
appending the next search to the inclusive historical purple maximum. -/
theorem select_next (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P) (q : Point) :
    select t lo searches P q (blue t lo searched q.1) = value t lo (searches ++ [searched]) P q := by
  by_cases active : Active P q
  · have age : q.2 ≤ searches.length := (history q active.1).2.le
    by_cases external : External P q
    · rw [(external_spec t lo (searches ++ [searched]) external).2]
      simp only [select, active, not_true_eq_false, ite_false, external, ite_true,
        currentBlue, List.getLast?_append, List.getLast?_singleton, Option.some_or]
    · by_cases glancing : Glancing P q
      · rw [(glancing_spec t lo (searches ++ [searched]) glancing).2,
          purple_step t lo searches searched q.2 q.1 age]
        simp only [select, active, not_true_eq_false, ite_false, external, glancing, ite_true]
      · rw [(internal_spec t lo (searches ++ [searched]) ⟨active, external, glancing⟩).2]
        simp only [select, active, not_true_eq_false, ite_false, external, glancing]
  · simp [select, value, color, active]

theorem item_initial (t : Tree) (lo : Nat) (prior : List Nat) (old : Nat)
    {n : Nat} {P : Finset Point} (history : History n (prior.length + 1) P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (x : Nat) :
    itemAt t lo (prior ++ [old]) P (forest t lo old) x = itemValue t lo (prior ++ [old]) P x := by
  cases recent : latest P x with
  | none => simp [itemAt, itemValue, recent]
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    simp only [itemAt, itemValue, recent, valueAt,
      rootBlue_forest t lo old x (valid _ active.1)]
    exact select_current t lo prior old history (x, stamp)

theorem item_final (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (x : Nat) :
    itemAt t lo searches P (forest t lo searched) x = itemValue t lo (searches ++ [searched]) P x := by
  cases recent : latest P x with
  | none => simp [itemAt, itemValue, recent]
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    simp only [itemAt, itemValue, recent, valueAt,
      rootBlue_forest t lo searched x (valid _ active.1)]
    exact select_next t lo searches searched history (x, stamp)

theorem total_initial (t : Tree) (lo : Nat) (prior : List Nat) (old : Nat)
    {n : Nat} {P : Finset Point} (history : History n (prior.length + 1) P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAt t lo (prior ++ [old]) P (forest t lo old) domain = totalAmount t lo (prior ++ [old]) P domain := by
  unfold totalAt totalAmount
  apply Finset.sum_congr rfl
  intro x _
  simp only [amountAt, itemAmount, item_initial t lo prior old history valid x]

theorem total_final (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (domain : Finset Nat) :
    totalAt t lo searches P (forest t lo searched) domain = totalAmount t lo (searches ++ [searched]) P domain := by
  unfold totalAt totalAmount
  apply Finset.sum_congr rfl
  intro x _
  simp only [amountAt, itemAmount, item_final t lo searches searched history valid x]

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
