module

public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Definitions.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Geometry
public import RotationBST.Algorithms.GreedyASS.Potential.Colors
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting
open Items Reference

theorem purple_point (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat)
    (colored : itemColor t lo searches P x = some .purple) :
    ∃ stamp, Active P (x, stamp) ∧ Glancing P (x, stamp) ∧
      color t lo searches P (x, stamp) = some .purple := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at colored
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have pointColor : color t lo searches P (x, stamp) = some .purple := by
      simpa only [itemColor, recent] using colored
    refine ⟨stamp, active, ?_, pointColor⟩
    simp only [color, active, not_true_eq_false, ↓reduceIte] at pointColor
    split at pointColor
    · split at pointColor
      · cases pointColor
      · split at pointColor <;> cases pointColor
    · split at pointColor
      · assumption
      · cases pointColor

/-- Three ordered glancing items in one current component force the middle
one to be red: its red value is below current blue, hence below purple. -/
theorem middle_red (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) {p q r : Point}
    (left : Glancing P p) (middle : Glancing P q) (right : Glancing P r)
    (insideP : c.Contains p.1) (insideQ : c.Contains q.1) (insideR : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    color t lo (searches ++ [searched]) P q = some .red := by
  obtain ⟨a, b, ha, hb, pa, aq, qb, br⟩ := bracket satisfied left middle right pq qr
  have nested := Distance.enclosing t lo q.1 p.1 a b r.1 pa (by omega) br
  have bounds := Reference.bounds t lo searched component
  have validP : lo ≤ p.1 ∧ p.1 < lo + leaves t := by
    unfold Component.Contains at insideP
    omega
  have validR : lo ≤ r.1 ∧ r.1 < lo + leaves t := by
    unfold Component.Contains at insideR
    omega
  have rootBound := (Distance.forest_compare t lo searched p.1 q.1 r.1 component insideQ
    pq.le qr.le validP validR).mpr ⟨insideP, insideR⟩
  have blueRoot := blue_component t lo searched q.1 component insideQ
  have active : Active P q := middle.elim (fun h => h.1) (fun h => h.1)
  have age : q.2 ≤ searches.length := by have := (history q active.1).2; omega
  have historical := purple_ge_blue t lo searches searched q.2 q.1 age
  have below : red t lo P q < WithTop.some (purple t lo (searches ++ [searched]) q.2 q.1) := by
    have numeric : Distance.toLCA t lo q.1 a b < purple t lo (searches ++ [searched]) q.2 q.1 := by omega
    simpa only [red, ha, hb, WithTop.coe_lt_coe] using numeric
  simpa only [below, ↓reduceIte] using (glancing_spec t lo (searches ++ [searched]) middle).1

theorem card_le_two (s : Finset Nat)
    (noTriple : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a < b → b < c → False) : s.card ≤ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | nonempty
  · simp
  have cover : s ⊆ {s.min' nonempty, s.max' nonempty} := by
    intro x hx
    by_cases first : x = s.min' nonempty
    · simp [first]
    by_cases last : x = s.max' nonempty
    · simp [last]
    have lower := Finset.min'_le s x hx
    have upper := Finset.le_max' s x hx
    exact (noTriple _ (Finset.min'_mem s nonempty) x hx _ (Finset.max'_mem s nonempty)
      (by omega) (by omega)).elim
  exact (Finset.card_le_card cover).trans Finset.card_le_two

/-- The purple half of Lemma 3.1, for the actual coloring and historical
maximum, not for an abstract set of assumed purple labels. -/
theorem purple_count (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (purpleKeys t lo (searches ++ [searched]) P c).card ≤ 2 := by
  apply card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨_, cx, colorX⟩ := Finset.mem_filter.mp hx
  obtain ⟨_, cy, colorY⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, cz, colorZ⟩ := Finset.mem_filter.mp hz
  obtain ⟨tx, _, gx, _⟩ := purple_point t lo (searches ++ [searched]) P x colorX
  obtain ⟨ty, _, gy, purpleY⟩ := purple_point t lo (searches ++ [searched]) P y colorY
  obtain ⟨tz, _, gz, _⟩ := purple_point t lo (searches ++ [searched]) P z colorZ
  have redY := middle_red t lo searches searched satisfied history component
    gx gy gz cx cy cz xy yz
  rw [redY] at purpleY
  cases purpleY

end RotationBST.Geometric.GreedyASS.Potential.Counting
