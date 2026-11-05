module

public import RotationBST.Algorithms.GreedyASS.Virgin.History
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Virgin
open Reference

theorem keys_nonempty (history : List Nat) (request : Nat) : (keys history request).Nonempty :=
  ⟨request, by simp [keys, greedySweep]⟩

theorem touched_member {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (member : c ∈ touched t lo history request) : c ∈ forest t lo request := by
  classical
  exact List.mem_toFinset.mp (Finset.mem_filter.mp member).1

theorem old_touched_member {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (member : c ∈ oldTouched t lo history request) : c ∈ forest t lo request := by
  classical
  exact touched_member (Finset.mem_filter.mp member).1

/-- A touched old component contains an extreme access of the new row.
Thus it cannot sit strictly between two other touched components. -/
theorem extreme {t : Tree} {lo request : Nat} {history : List Nat} {c : Component}
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t)
    (member : c ∈ oldTouched t lo history request) :
    c.Contains ((keys history request).min' (keys_nonempty history request)) ∨
      c.Contains ((keys history request).max' (keys_nonempty history request)) := by
  classical
  simp only [oldTouched, touched, Finset.mem_filter, List.mem_toFinset] at member
  obtain ⟨⟨_, x, hx, inside⟩, old⟩ := member
  obtain ⟨accessed, within, side⟩ := old_barrier valid old
  rcases side with left | right
  · right
    have upper := left _ (Finset.max'_mem _ (keys_nonempty history request))
    have lower := Finset.le_max' (keys history request) x hx
    exact ⟨le_trans inside.1 lower, lt_of_le_of_lt upper within.2⟩
  · left
    have lower := right _ (Finset.min'_mem _ (keys_nonempty history request))
    have upper := Finset.min'_le (keys history request) x hx
    exact ⟨le_trans within.1 lower, lt_of_le_of_lt upper inside.2⟩

private theorem same_owner {t : Tree} {lo request key : Nat} {a b : Component}
    (ma : a ∈ forest t lo request) (mb : b ∈ forest t lo request)
    (ca : a.Contains key) (cb : b.Contains key) : a = b := by
  have range := bounds t lo request ma
  obtain ⟨owner, _, unique⟩ := partition t lo request key
    ⟨le_trans range.1 ca.1, lt_of_lt_of_le ca.2 range.2⟩
  exact (unique a ⟨ma, ca⟩).trans (unique b ⟨mb, cb⟩).symm

/-- Lemma 3.7: at most two previously accessed components are touched on
the new row. The proof includes the searched singleton without an exception. -/
theorem count (t : Tree) (lo : Nat) (history : List Nat) (request : Nat)
    (valid : ∀ x ∈ history ++ [request], lo ≤ x ∧ x < lo + leaves t) :
    (oldTouched t lo history request).card ≤ 2 := by
  classical
  let old := oldTouched t lo history request
  let left := old.filter fun c => c.Contains ((keys history request).min' (keys_nonempty history request))
  let right := old.filter fun c => c.Contains ((keys history request).max' (keys_nonempty history request))
  have leftSmall : left.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ma, ca⟩ := Finset.mem_filter.mp ha
    obtain ⟨mb, cb⟩ := Finset.mem_filter.mp hb
    exact same_owner (old_touched_member ma) (old_touched_member mb) ca cb
  have rightSmall : right.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ma, ca⟩ := Finset.mem_filter.mp ha
    obtain ⟨mb, cb⟩ := Finset.mem_filter.mp hb
    exact same_owner (old_touched_member ma) (old_touched_member mb) ca cb
  have covered : old ⊆ left ∪ right := by
    intro c hc
    rcases extreme valid hc with left | right
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, left⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, right⟩)
  have bounded := (Finset.card_le_card covered).trans (Finset.card_union_le left right)
  change old.card ≤ 2
  omega

end RotationBST.Geometric.GreedyASS.Virgin
