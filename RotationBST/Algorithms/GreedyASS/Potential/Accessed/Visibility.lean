module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Top
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

/-- Any projected old access comes from its column's most recent point. -/
theorem access_visible {n time searched : Nat} {P : Finset Point}
    (history : History n time P) {q : Point} (active : Active P q)
    (accessed : q.1 ∈ greedySweep time searched P) (different : q.1 ≠ searched) :
    Visible P time searched q := by
  have projected : q.1 ∈ (P.filter (Visible P time searched)).image Prod.fst :=
    (Finset.mem_insert.mp accessed).resolve_left different
  obtain ⟨p, hp, same⟩ := Finset.mem_image.mp projected
  obtain ⟨member, visible⟩ := Finset.mem_filter.mp hp
  have lower := active.2 p member same
  have age := (history q active.1).2
  have equal : p = q := by
    by_contra distinct
    apply visible.2 q active.1 (Ne.symm distinct)
    simp only [Rectangle, same]
    exact ⟨min_le_left _ _, le_max_left _ _, (min_le_left _ _).trans lower,
      age.le.trans (le_max_right _ _)⟩
  simpa only [equal] using visible

/-- Same-row neighbors block a projection unless the new search lies
strictly between them. This also covers the searched item itself. -/
theorem search_between {n time searched : Nat} {P : Finset Point}
    (history : History n time P) {q : Point} (active : Active P q)
    (accessed : q.1 ∈ greedySweep time searched P) {a b : Nat}
    (left : leftNeighbor P q = some a) (right : rightNeighbor P q = some b) :
    a < searched ∧ searched < b := by
  have ha := (left_spec P q a).mp left
  have hb := (right_spec P q b).mp right
  by_cases same : q.1 = searched
  · simpa only [same] using And.intro ha.2.1 hb.2.1
  · have visible := access_visible history active accessed same
    have age := (history q active.1).2
    constructor
    · by_contra outside
      have bound : searched ≤ a := Nat.le_of_not_gt outside
      apply visible.2 (a, q.2) ha.1 (by intro eq; have := congrArg Prod.fst eq; simp only at this; omega)
      simp only [Rectangle]
      exact ⟨(min_le_right _ _).trans bound, ha.2.1.le.trans (le_max_left _ _),
        min_le_left _ _, le_max_left _ _⟩
    · by_contra outside
      have bound : b ≤ searched := Nat.le_of_not_gt outside
      apply visible.2 (b, q.2) hb.1 (by intro eq; have := congrArg Prod.fst eq; simp only at this; omega)
      simp only [Rectangle]
      exact ⟨(min_le_left _ _).trans hb.2.1.le, bound.trans (le_max_right _ _),
        min_le_left _ _, le_max_left _ _⟩

/-- If a nontrivial leaf interval contains both the item and current search,
its LCA lies strictly above the item's current component root. -/
theorem blue_enclosed (t : Tree) (lo searched x a b : Nat)
    (ax : a < x) (xb : x < b) (as : a ≤ searched) (sb : searched ≤ b)
    (validA : lo ≤ a ∧ a < lo + leaves t) (validB : lo ≤ b ∧ b < lo + leaves t) :
    blue t lo searched x ≤ Distance.toLCA t lo x a b := by
  have validX : lo ≤ x ∧ x < lo + leaves t := by omega
  have validSearch : lo ≤ searched ∧ searched < lo + leaves t := by omega
  obtain ⟨c, member, inside⟩ := covers t lo searched x validX
  have outside : ¬ c.Contains a ∨ ¬ c.Contains b := by
    by_cases ca : c.Contains a
    · right
      intro cb
      have cs : c.Contains searched := ⟨ca.1.trans as, sb.trans_lt cb.2⟩
      have singleton := contains_searched t lo searched validSearch member cs
      rw [singleton] at ca cb
      simp only [Component.Contains, Component.last, leaves] at ca cb
      omega
    · exact Or.inl ca
  have height := (Distance.forest_outside t lo searched a x b member inside ax.le xb.le validA validB).mpr outside
  rw [blue_component t lo searched x member inside]
  omega

/-- The red candidate of any accessed nonexternal old point covers the
current blue value. No arboral-satisfaction hypothesis is needed here. -/
theorem red_covers_blue (t : Tree) (lo searched : Nat) {n time : Nat} {P : Finset Point}
    (history : History n time P) (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t)
    {q : Point} (active : Active P q) (nonexternal : ¬ External P q)
    (accessed : q.1 ∈ greedySweep time searched P) :
    WithTop.some (blue t lo searched q.1) ≤ red t lo P q := by
  obtain ⟨a, b, left, right, ax, xb, value⟩ := red_finite t lo active nonexternal
  obtain ⟨as, sb⟩ := search_between history active accessed left right
  have validA := valid (a, q.2) ((left_spec P q a).mp left).1
  have validB := valid (b, q.2) ((right_spec P q b).mp right).1
  rw [value]
  exact WithTop.coe_le_coe.mpr (blue_enclosed t lo searched q.1 a b ax xb as.le sb.le validA validB)

/-- Lemma 3.12 for the executable greedy sweep, including the searched key
and the strict decrease when the new color remains red. -/
theorem red_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .red) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x <
          itemValue t lo (searches ++ [searched]) P x) := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at old
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have colored : color t lo (searches ++ [searched]) P (x, stamp) = some .red := by
      simpa only [itemColor, recent] using old
    have nonexternal : ¬ External P (x, stamp) := by
      intro external
      have spec := (external_spec t lo (searches ++ [searched]) external).1
      rw [spec] at colored
      split at colored
      · contradiction
      · split at colored <;> contradiction
    have valued : itemValue t lo (searches ++ [searched]) P x = red t lo P (x, stamp) := by
      simp [itemValue, recent, value, colored]
    have bound := red_covers_blue t lo searched history valid active nonexternal member
    obtain ⟨weak, strict⟩ := top_bound t lo searches searched _ history member
    rw [valued]
    exact ⟨weak.trans bound, fun red => (strict red).trans_le bound⟩

end RotationBST.Geometric.GreedyASS.Potential.Accessed
