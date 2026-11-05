module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Neighbors
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

/-- If a new access has row neighbors in an enclosing interval, its
selected potential is bounded by the red candidate of that interval. -/
theorem new_bracket_bound (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n searches.length P)
    {a x b : Nat} (ha : a ∈ keys) (hx : x ∈ keys) (hb : b ∈ keys) (ax : a < x) (xb : x < b) :
    itemAmount t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
      Distance.toLCA t lo x a b := by
  have active := top_active keys history hx
  have nonexternal : ¬ External (P ∪ row searches.length keys) (x, searches.length) := by
    rintro (left | right)
    · have order := (top_left keys history hx).mp left a ha
      omega
    · have order := (top_right keys history hx).mp right b hb
      omega
  have glancing : Glancing (P ∪ row searches.length keys) (x, searches.length) :=
    Or.inl (top_glancing keys history hx nonexternal).1
  obtain ⟨u, v, left, right, ux, xv, redValue⟩ := red_finite t lo active nonexternal
  have au := ((left_spec (P ∪ row searches.length keys) (x, searches.length) u).mp left).2.2 a
    (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨ha, rfl⟩)) ax
  have vb := ((right_spec (P ∪ row searches.length keys) (x, searches.length) v).mp right).2.2 b
    (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hb, rfl⟩)) xb
  have enclosed := Distance.enclosing t lo x a u v b au (by omega) vb
  have bound : itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
      WithTop.some (Distance.toLCA t lo x a b) := by
    rw [(item_spec t lo (searches ++ [searched]) active).2,
      (glancing_spec t lo (searches ++ [searched]) glancing).2, redValue]
    exact (min_le_left _ _).trans (WithTop.coe_le_coe.mpr enclosed)
  rw [amount_exact] at bound
  exact WithTop.coe_le_coe.mp bound

/-- A finite green candidate has both external neighbors. -/
theorem green_neighbors (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (colored : color t lo searches P q = some .green) :
    ∃ a b, leftExternal P q.1 = some a ∧ rightExternal P q.1 = some b := by
  have below := (green_spec t lo searches colored).2.2.1
  cases left : leftExternal P q.1 with
  | none => simp [green, left] at below
  | some a =>
    cases right : rightExternal P q.1 with
    | none => simp [green, left, right] at below
    | some b => exact ⟨a, b, rfl, rfl⟩

/-- Green places both external neighbors within the reference component,
so the next search is outside their interval. The distance comparison
also covers the searched-singleton boundary without a separate exception. -/
theorem green_search_outside (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {P : Finset Point} (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {q : Point}
    (colored : color t lo (searches ++ [searched]) P q = some .green) {a b : Nat}
    (left : leftExternal P q.1 = some a) (right : rightExternal P q.1 = some b) :
    searched < a ∨ b < searched := by
  have below := (green_spec t lo (searches ++ [searched]) colored).2.2.1
  have ha := (left_external_spec P q.1 a).mp left
  have hb := (right_external_spec P q.1 b).mp right
  obtain ⟨ta, ea⟩ := (mem_external P a).mp ha.1
  obtain ⟨tb, eb⟩ := (mem_external P b).mp hb.1
  have validA := valid (a, ta) (ea.elim (fun h => h.1.1) (fun h => h.1.1))
  have validB := valid (b, tb) (eb.elim (fun h => h.1.1) (fun h => h.1.1))
  have current : currentBlue t lo (searches ++ [searched]) q.1 = blue t lo searched q.1 := by
    simp [currentBlue]
  have numeric : Distance.toLCA t lo q.1 a b + 1 ≤ blue t lo searched q.1 := by
    simpa only [green, left, right, current, WithTop.coe_le_coe] using below
  by_contra inside
  have lower : a ≤ searched := by omega
  have upper : searched ≤ b := by omega
  have enclosed := blue_enclosed t lo searched q.1 a b ha.2.1 hb.2.1 lower upper validA validB
  omega

/-- Lemma 3.9 in the inequality form needed for amortization: an accessed
item that was green at the intermediate snapshot loses at least one unit. -/
theorem green_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .green) :
    itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x + 1 ≤
      itemAmount t lo (searches ++ [searched]) P x := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at old
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have colored : color t lo (searches ++ [searched]) P (x, stamp) = some .green := by
      simpa only [itemColor, recent] using old
    obtain ⟨external, notTop, _, valued⟩ := green_spec t lo (searches ++ [searched]) colored
    obtain ⟨a, b, left, right⟩ := green_neighbors t lo (searches ++ [searched]) colored
    have ha := (left_external_spec P x a).mp left
    have hb := (right_external_spec P x b).mp right
    have outside := green_search_outside t lo searches searched valid colored left right
    obtain ⟨accessA, accessB, _⟩ := external_access_bracket satisfied history external notTop member left right outside
    have after := new_bracket_bound t lo searches searched _ history accessA member accessB ha.2.1 hb.2.1
    have before : itemAmount t lo (searches ++ [searched]) P x = Distance.toLCA t lo x a b + 1 := by
      have equal := (item_spec t lo (searches ++ [searched]) active).2.trans valued
      rw [green, left, right, amount_exact] at equal
      exact WithTop.coe_inj.mp equal
    omega

end RotationBST.Geometric.GreedyASS.Potential.Accessed
