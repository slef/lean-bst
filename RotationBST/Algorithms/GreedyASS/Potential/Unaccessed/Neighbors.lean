module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Sides
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- External-key membership is unchanged in an untouched column. -/
theorem external_key_unchanged {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (untouched : x ∉ keys) :
    x ∈ externalKeys (P ∪ row time keys) ↔ x ∈ externalKeys P := by
  constructor
  · intro member
    obtain ⟨stamp, external⟩ := (mem_external _ x).mp member
    have active := external.elim (fun h => h.1) (fun h => h.1)
    have oldActive := (active_unchanged P time keys (x, stamp) untouched).mp active
    exact (mem_external P x).mpr ⟨stamp, (external_unchanged keys history oldActive untouched).mp external⟩
  · intro member
    obtain ⟨stamp, external⟩ := (mem_external P x).mp member
    have active := external.elim (fun h => h.1) (fun h => h.1)
    exact (mem_external _ x).mpr ⟨stamp, (external_unchanged keys history active untouched).mpr external⟩

/-- A row entirely to the right leaves the left external query unchanged,
including when that query is undefined. -/
theorem left_fixed {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) (x : Nat) (side : ∀ y ∈ keys, x < y) :
    leftExternal (P ∪ row time keys) x = leftExternal P x := by
  unfold leftExternal
  congr 1
  ext y
  simp only [Finset.mem_filter]
  by_cases left : y < x
  · have untouched : y ∉ keys := by intro hy; have := side y hy; omega
    rw [external_key_unchanged keys history untouched]
  · simp [left]

theorem right_fixed {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) (x : Nat) (side : ∀ y ∈ keys, y < x) :
    rightExternal (P ∪ row time keys) x = rightExternal P x := by
  unfold rightExternal
  congr 1
  ext y
  simp only [Finset.mem_filter]
  by_cases right : x < y
  · have untouched : y ∉ keys := by intro hy; have := side y hy; omega
    rw [external_key_unchanged keys history untouched]
  · simp [right]

/-- An accessed right neighbor is replaced by the leftmost new access;
an untouched neighbor remains external at its old point. -/
theorem right_witness {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} {q : Point} (external : External P q)
    (xq : x < q.1) (side : ∀ y ∈ keys, x < y) :
    ∃ p, External (P ∪ row time keys) p ∧ x < p.1 ∧ p.1 ≤ q.1 := by
  by_cases touched : q.1 ∈ keys
  · have nonempty : keys.Nonempty := ⟨q.1, touched⟩
    let y := keys.min' nonempty
    have member : y ∈ keys := Finset.min'_mem _ _
    have least : ∀ z ∈ keys, y ≤ z := fun z hz => Finset.min'_le _ z hz
    exact ⟨(y, time), Or.inl ((top_left keys history member).mpr least),
      side y member, least q.1 touched⟩
  · have active := external.elim (fun h => h.1) (fun h => h.1)
    exact ⟨q, (external_unchanged keys history active touched).mpr external, xq, le_rfl⟩

theorem left_witness {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} {q : Point} (external : External P q)
    (qx : q.1 < x) (side : ∀ y ∈ keys, y < x) :
    ∃ p, External (P ∪ row time keys) p ∧ q.1 ≤ p.1 ∧ p.1 < x := by
  by_cases touched : q.1 ∈ keys
  · have nonempty : keys.Nonempty := ⟨q.1, touched⟩
    let y := keys.max' nonempty
    have member : y ∈ keys := Finset.max'_mem _ _
    have greatest : ∀ z ∈ keys, z ≤ y := fun z hz => Finset.le_max' _ z hz
    exact ⟨(y, time), Or.inr ((top_right keys history member).mpr greatest),
      greatest q.1 touched, side y member⟩
  · have active := external.elim (fun h => h.1) (fun h => h.1)
    exact ⟨q, (external_unchanged keys history active touched).mpr external, le_rfl, qx⟩

/-- A row lying on one side of an unaccessed item can only shrink the
interval of its defined external neighbors. -/
theorem neighbors_nested {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x a b : Nat}
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (side : (∀ y ∈ keys, y < x) ∨ (∀ y ∈ keys, x < y)) :
    ∃ u v, leftExternal (P ∪ row time keys) x = some u ∧
      rightExternal (P ∪ row time keys) x = some v ∧ a ≤ u ∧ u < x ∧ x < v ∧ v ≤ b := by
  have ha := (left_external_spec P x a).mp left
  have hb := (right_external_spec P x b).mp right
  obtain ⟨ta, ea⟩ := (mem_external P a).mp ha.1
  obtain ⟨tb, eb⟩ := (mem_external P b).mp hb.1
  rcases side with side | side
  · obtain ⟨p, ep, ap, px⟩ := left_witness keys history ea ha.2.1 side
    have untouched : b ∉ keys := by intro member; have := side b member; have := hb.2.1; omega
    have activeB := eb.elim (fun h => h.1) (fun h => h.1)
    have newB := (external_unchanged keys history activeB untouched).mpr eb
    obtain ⟨u, v, hu, hv, pu, ux, xv, vb⟩ := external_bracket (q := (x, time)) ep newB px hb.2.1
    exact ⟨u, v, hu, hv, ap.trans pu, ux, xv, vb⟩
  · obtain ⟨p, ep, xp, pb⟩ := right_witness keys history eb hb.2.1 side
    have untouched : a ∉ keys := by intro member; have := side a member; have := ha.2.1; omega
    have activeA := ea.elim (fun h => h.1) (fun h => h.1)
    have newA := (external_unchanged keys history activeA untouched).mpr ea
    obtain ⟨u, v, hu, hv, au, ux, xv, vp⟩ := external_bracket (q := (x, time)) newA ep ha.2.1 xp
    exact ⟨u, v, hu, hv, au, ux, xv, vp.trans pb⟩

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
