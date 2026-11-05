module

public import RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Items.Updates
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

theorem mem_external (P : Finset Point) (x : Nat) :
    x ∈ externalKeys P ↔ ∃ stamp, External P (x, stamp) := by
  constructor
  · intro member
    obtain ⟨q, hq, eq⟩ := Finset.mem_image.mp member
    have external := (Finset.mem_filter.mp hq).2
    exact ⟨q.2, by simpa only [← eq] using external⟩
  · rintro ⟨stamp, external⟩
    have member : (x, stamp) ∈ P := external.elim (fun h => h.1.1) (fun h => h.1.1)
    exact Finset.mem_image.mpr ⟨(x, stamp), Finset.mem_filter.mpr ⟨member, external⟩, rfl⟩

theorem left_external_spec (P : Finset Point) (x a : Nat) :
    leftExternal P x = some a ↔ a ∈ externalKeys P ∧ a < x ∧
      ∀ y ∈ externalKeys P, y < x → y ≤ a := by
  simp only [leftExternal, greatest_some, Finset.mem_filter]
  aesop

theorem right_external_spec (P : Finset Point) (x b : Nat) :
    rightExternal P x = some b ↔ b ∈ externalKeys P ∧ x < b ∧
      ∀ y ∈ externalKeys P, x < y → b ≤ y := by
  simp only [rightExternal, least_some, Finset.mem_filter]
  aesop

theorem red_finite (t : Tree) (lo : Nat) {P : Finset Point} {q : Point}
    (active : Active P q) (nonexternal : ¬ External P q) :
    ∃ a b, leftNeighbor P q = some a ∧ rightNeighbor P q = some b ∧
      a < q.1 ∧ q.1 < b ∧ red t lo P q = (Distance.toLCA t lo q.1 a b : Nat) := by
  obtain ⟨a, b, left, right⟩ := neighbors_exist active nonexternal
  exact ⟨a, b, left, right, ((left_spec P q a).mp left).2.1,
    ((right_spec P q b).mp right).2.1, by simp [red, left, right]⟩

/-- Lemma 3.14: adding a later row leaves the red candidate at an old point
unchanged. If its column is unaccessed, that point remains the active one. -/
theorem red_unchanged (t : Tree) (lo : Nat) {n time : Nat} {P : Finset Point}
    (keys : Finset Nat) (history : History n time P) {q : Point} (member : q ∈ P) :
    red t lo (P ∪ row time keys) q = red t lo P q := by
  obtain ⟨left, right⟩ := neighbors_unchanged keys history member
  simp only [red, left, right]

theorem external_bracket {P : Finset Point} {p q r : Point}
    (left : External P p) (right : External P r) (pq : p.1 < q.1) (qr : q.1 < r.1) :
    ∃ a b, leftExternal P q.1 = some a ∧ rightExternal P q.1 = some b ∧
      p.1 ≤ a ∧ a < q.1 ∧ q.1 < b ∧ b ≤ r.1 := by
  have hp : p.1 ∈ externalKeys P := (mem_external P p.1).mpr ⟨p.2, left⟩
  have hr : r.1 ∈ externalKeys P := (mem_external P r.1).mpr ⟨r.2, right⟩
  have nl : ((externalKeys P).filter fun x => x < q.1).Nonempty :=
    ⟨p.1, Finset.mem_filter.mpr ⟨hp, pq⟩⟩
  have nr : ((externalKeys P).filter fun x => q.1 < x).Nonempty :=
    ⟨r.1, Finset.mem_filter.mpr ⟨hr, qr⟩⟩
  let a := ((externalKeys P).filter fun x => x < q.1).max' nl
  let b := ((externalKeys P).filter fun x => q.1 < x).min' nr
  have ha : leftExternal P q.1 = some a := by simp [leftExternal, greatest, nl, a]
  have hb : rightExternal P q.1 = some b := by simp [rightExternal, least, nr, b]
  have la := (left_external_spec P q.1 a).mp ha
  have rb := (right_external_spec P q.1 b).mp hb
  exact ⟨a, b, ha, hb, la.2.2 p.1 hp pq, la.2.1, rb.2.1, rb.2.2 r.1 hr qr⟩

end RotationBST.Geometric.GreedyASS.Potential
