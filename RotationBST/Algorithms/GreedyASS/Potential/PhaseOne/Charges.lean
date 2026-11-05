module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Values
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Blue
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

/-- The middle of three glancing points in any actual reference subtree
has red strictly below that subtree's blue candidate. No search-root premise
or intermediate color assignment is needed. -/
theorem glancing_middle {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P)
    {p q r : Point} (left : Glancing P p) (middle : Glancing P q) (right : Glancing P r)
    (cp : c.Contains p.1) (cq : c.Contains q.1) (cr : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    red t lo P q < WithTop.some (Distance.toRoot c q.1 + 1) := by
  obtain ⟨a, b, ha, hb, pa, aq, qb, br⟩ := Counting.bracket satisfied left middle right pq qr
  have nested := Distance.enclosing t lo q.1 p.1 a b r.1 pa (by omega) br
  have rootBound := (occurrence.compare cq pq.le qr.le (occurrence.valid cp) (occurrence.valid cr)).mpr ⟨cp, cr⟩
  simp only [red, ha, hb, WithTop.coe_lt_coe]
  omega

theorem external_middle {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} {p q r : Point}
    (left : External P p) (right : External P r)
    (cp : c.Contains p.1) (cq : c.Contains q.1) (cr : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    green t lo P q.1 ≤ WithTop.some (Distance.toRoot c q.1 + 1) := by
  obtain ⟨a, b, ha, hb, pa, aq, qb, br⟩ := external_bracket (q := q) left right pq qr
  have nested := Distance.enclosing t lo q.1 p.1 a b r.1 pa (by omega) br
  have rootBound := (occurrence.compare cq pq.le qr.le (occurrence.valid cp) (occurrence.valid cr)).mpr ⟨cp, cr⟩
  simp only [green, ha, hb, WithTop.coe_le_coe]
  omega

theorem glancing_count {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P) :
    ((P.filter fun q => c.Contains q.1 ∧ Glancing P q ∧
      WithTop.some (Distance.toRoot c q.1 + 1) < red t lo P q).image Prod.fst).card ≤ 2 := by
  apply Counting.card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨_, cp, gp, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, cq, gq, charge⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, cr, gr, _⟩ := Finset.mem_filter.mp hr
  exact (lt_asymm charge (glancing_middle occurrence satisfied gp gq gr cp cq cr xy yz))

theorem left_count {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P) :
    ((P.filter fun q => c.Contains q.1 ∧ LeftExternal P q ∧
      (LatestRow P q.2 ∨ WithTop.some (Distance.toRoot c q.1 + 1) < green t lo P q.1)).image Prod.fst).card ≤ 2 := by
  apply Counting.card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨_, cp, ep, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, cq, eq, charge⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, cr, er, _⟩ := Finset.mem_filter.mp hr
  have capped := external_middle occurrence (Or.inl ep) (Or.inl er) cp cq cr xy yz
  rcases charge with top | greater
  · exact left_not_latest satisfied eq.1 er yz top
  · exact (not_lt_of_ge capped) greater

theorem right_count {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P) :
    ((P.filter fun q => c.Contains q.1 ∧ RightExternal P q ∧
      (LatestRow P q.2 ∨ WithTop.some (Distance.toRoot c q.1 + 1) < green t lo P q.1)).image Prod.fst).card ≤ 2 := by
  apply Counting.card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨_, cp, ep, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, cq, eq, charge⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, cr, er, _⟩ := Finset.mem_filter.mp hr
  have capped := external_middle occurrence (Or.inr ep) (Or.inr er) cp cq cr xy yz
  rcases charge with top | greater
  · exact right_not_latest satisfied eq.1 ep xy top
  · exact (not_lt_of_ge capped) greater

/-- At most six active columns in any reference subtree can gain potential
when its root moves upward. This applies to arbitrary intermediate cuts. -/
theorem charged_count {t : Tree} {lo k : Nat} {c : Component}
    (occurrence : Distance.Occurs t lo c k) {P : Finset Point} (satisfied : ASS P) :
    (chargedKeys t lo P c).card ≤ 6 := by
  let left := (P.filter fun q => c.Contains q.1 ∧ LeftExternal P q ∧
    (LatestRow P q.2 ∨ WithTop.some (Distance.toRoot c q.1 + 1) < green t lo P q.1)).image Prod.fst
  let right := (P.filter fun q => c.Contains q.1 ∧ RightExternal P q ∧
    (LatestRow P q.2 ∨ WithTop.some (Distance.toRoot c q.1 + 1) < green t lo P q.1)).image Prod.fst
  let glancing := (P.filter fun q => c.Contains q.1 ∧ Glancing P q ∧
    WithTop.some (Distance.toRoot c q.1 + 1) < red t lo P q).image Prod.fst
  have cover : chargedKeys t lo P c ⊆ (left ∪ right) ∪ glancing := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨member, _, inside, sensitive⟩ := Finset.mem_filter.mp hq
    rcases sensitive with ⟨external, candidate⟩ | ⟨glance, candidate⟩
    · apply Finset.mem_union_left
      rcases external with ext | ext
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨q, Finset.mem_filter.mpr ⟨member, inside, ext, candidate⟩, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨q, Finset.mem_filter.mpr ⟨member, inside, ext, candidate⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨member, inside, glance, candidate⟩, rfl⟩)
  have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have directions := Finset.card_union_le left right
  have lc : left.card ≤ 2 := left_count occurrence satisfied
  have rc : right.card ≤ 2 := right_count occurrence satisfied
  have gc : glancing.card ≤ 2 := glancing_count occurrence satisfied
  omega

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
