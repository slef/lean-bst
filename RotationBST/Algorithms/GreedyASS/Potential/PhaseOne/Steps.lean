module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Endpoints
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Charges
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- Outside the two charged child sets, a merge either leaves the owner
unchanged or the selected potential is already capped by red or green. -/
theorem merge_capped (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (before after : List Component) (first : Nat) (l r : Tree)
    (cut : Transitions.Cut t lo (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after))
    (admissible : Transitions.Admissible t lo (.merge first l r)) {q : Point}
    (active : Active P q) (valid : lo ≤ q.1 ∧ q.1 < lo + leaves t)
    (uncharged : q.1 ∉ chargedKeys t lo P ⟨first, l⟩ ∪ chargedKeys t lo P ⟨first + leaves l, r⟩) :
    valueAt t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) q ≤
      valueAt t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) q := by
  have step := Transitions.Step.merge before after first l r
  have nextCut := step.cut admissible cut
  obtain ⟨c, member, inside⟩ := cut.covers q.1 valid
  have oldBlue := rootBlue_component cut.ordered member inside
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (prior | rfl | rfl) | later
  · have newBlue := rootBlue_component nextCut.ordered
      (List.mem_append_left after (List.mem_append_left _ prior)) inside
    simp only [valueAt, oldBlue, newBlue, le_refl]
  · apply select_capped
    rw [oldBlue]
    intro sensitive
    apply uncharged
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨q, Finset.mem_filter.mpr ⟨active.1, active, inside, sensitive⟩, rfl⟩)
  · apply select_capped
    rw [oldBlue]
    intro sensitive
    apply uncharged
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨q, Finset.mem_filter.mpr ⟨active.1, active, inside, sensitive⟩, rfl⟩)
  · have newBlue := rootBlue_component nextCut.ordered (List.mem_append_right _ later) inside
    simp only [valueAt, oldBlue, newBlue, le_refl]

theorem merge_value (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (before after : List Component) (first : Nat) (l r : Tree)
    (cut : Transitions.Cut t lo (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after))
    (admissible : Transitions.Admissible t lo (.merge first l r)) {q : Point}
    (active : Active P q) (valid : lo ≤ q.1 ∧ q.1 < lo + leaves t) :
    valueAt t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) q ≤
      valueAt t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) q +
        WithTop.some (if q.1 ∈ chargedKeys t lo P ⟨first, l⟩ ∪ chargedKeys t lo P ⟨first + leaves l, r⟩ then 1 else 0) := by
  by_cases charged : q.1 ∈ chargedKeys t lo P ⟨first, l⟩ ∪ chargedKeys t lo P ⟨first + leaves l, r⟩
  · have blueBound := rootBlue_step cut (Transitions.Step.merge before after first l r) admissible valid
    simpa only [valueAt, charged, ite_true, WithTop.coe_one] using
      select_increment t lo searches P q blueBound
  · simpa only [charged, ite_false, WithTop.coe_zero, add_zero] using
      merge_capped t lo searches before after first l r cut admissible active valid charged

theorem merge_amount (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (before after : List Component) (first : Nat) (l r : Tree)
    (cut : Transitions.Cut t lo (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after))
    (admissible : Transitions.Admissible t lo (.merge first l r))
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (x : Nat) :
    amountAt t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) x ≤
      amountAt t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) x +
        (if x ∈ chargedKeys t lo P ⟨first, l⟩ ∪ chargedKeys t lo P ⟨first + leaves l, r⟩ then 1 else 0) := by
  cases recent : latest P x with
  | none => simp [amountAt, itemAt, recent]
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have bound := merge_value t lo searches before after first l r cut admissible active (valid _ active.1)
    have oldAmount := amount_exact t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) x
    have newAmount := amount_exact t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) x
    simp only [itemAt, recent] at oldAmount newAmount
    rw [oldAmount, newAmount, ← WithTop.coe_add] at bound
    exact WithTop.coe_le_coe.mp bound

theorem split_amount (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (before after : List Component) (first : Nat) (l r : Tree)
    (cut : Transitions.Cut t lo (before ++ [⟨first, .node l r⟩] ++ after))
    (admissible : Transitions.Admissible t lo (.split first l r))
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (x : Nat) :
    amountAt t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) x ≤
      amountAt t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) x := by
  cases recent : latest P x with
  | none => simp [amountAt, itemAt, recent]
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have blueBound := rootBlue_step cut (Transitions.Step.split before after first l r) admissible (valid _ active.1)
    have bound := select_mono t lo searches P (x, stamp) blueBound
    have oldAmount := amount_exact t lo searches P (before ++ [⟨first, .node l r⟩] ++ after) x
    have newAmount := amount_exact t lo searches P (before ++ [⟨first, l⟩, ⟨first + leaves l, r⟩] ++ after) x
    simp only [itemAt, recent, valueAt] at oldAmount newAmount
    rw [oldAmount, newAmount] at bound
    exact WithTop.coe_le_coe.mp bound

/-- A split cannot increase total item potential. A merge charges at most
one unit to each of at most six sensitive items in each old child. -/
theorem step_total (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point}
    (satisfied : ASS P) (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t)
    {roots next : List Component} {event : Transitions.Event}
    (cut : Transitions.Cut t lo roots) (step : Transitions.Step roots event next)
    (admissible : Transitions.Admissible t lo event) (domain : Finset Nat) :
    totalAt t lo searches P next domain ≤ totalAt t lo searches P roots domain +
      (if event.isMerge then 12 else 0) := by
  cases step with
  | split before after first l r =>
    simp only [Transitions.Event.isMerge, Bool.false_eq_true, ite_false, Nat.add_zero]
    unfold totalAt
    apply Finset.sum_le_sum
    intro x _
    exact split_amount t lo searches (P := P) before after first l r cut admissible valid x
  | merge before after first l r =>
    let charged := chargedKeys t lo P ⟨first, l⟩ ∪ chargedKeys t lo P ⟨first + leaves l, r⟩
    have sums := Finset.sum_le_sum (fun x (_ : x ∈ domain) =>
      merge_amount t lo searches (P := P) before after first l r cut admissible valid x)
    rw [Finset.sum_add_distrib, ← Finset.card_filter] at sums
    have subset : (domain.filter fun x => x ∈ charged) ⊆ charged := fun _ hx => (Finset.mem_filter.mp hx).2
    have chargeCount := Finset.card_le_card subset
    obtain ⟨kl, ol⟩ := cut.occurs ⟨first, l⟩ (by simp)
    obtain ⟨kr, occurrenceR⟩ := cut.occurs ⟨first + leaves l, r⟩ (by simp)
    have lc := charged_count ol satisfied
    have rc := charged_count occurrenceR satisfied
    have union := Finset.card_union_le (chargedKeys t lo P ⟨first, l⟩) (chargedKeys t lo P ⟨first + leaves l, r⟩)
    dsimp only [charged] at chargeCount
    simp only [Transitions.Event.isMerge, ite_true]
    unfold totalAt
    omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
