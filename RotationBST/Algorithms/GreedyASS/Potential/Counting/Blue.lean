module

public import RotationBST.Algorithms.GreedyASS.Potential.Counting.External
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting
open Items Reference

theorem blue_point (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat)
    (colored : itemColor t lo searches P x = some .blue) :
    ∃ stamp, Active P (x, stamp) ∧ External P (x, stamp) ∧
      color t lo searches P (x, stamp) = some .blue := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at colored
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have pointColor : color t lo searches P (x, stamp) = some .blue := by
      simpa only [itemColor, recent] using colored
    refine ⟨stamp, active, ?_, pointColor⟩
    simp only [color, active, not_true_eq_false, ↓reduceIte] at pointColor
    split at pointColor
    · assumption
    · split at pointColor
      · split at pointColor <;> cases pointColor
      · cases pointColor

theorem left_blue_count (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (_history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (leftBlueKeys t lo (searches ++ [searched]) P c).card ≤ 2 := by
  apply card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨_, cp, lp, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, cq, lq, blueQ⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, cr, lr, _⟩ := Finset.mem_filter.mp hr
  have notTop := left_not_latest satisfied lq.1 lr yz
  have greenQ := middle_green t lo searches searched component
    (Or.inl lp) (Or.inl lq) (Or.inl lr) cp cq cr xy yz notTop
  rw [greenQ] at blueQ
  cases blueQ

theorem right_blue_count (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (_history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (rightBlueKeys t lo (searches ++ [searched]) P c).card ≤ 2 := by
  apply card_le_two
  intro x hx y hy z hz xy yz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨_, cp, rp, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, cq, rq, blueQ⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, cr, rr, _⟩ := Finset.mem_filter.mp hr
  have notTop := right_not_latest satisfied rq.1 rp xy
  have greenQ := middle_green t lo searches searched component
    (Or.inr rp) (Or.inr rq) (Or.inr rr) cp cq cr xy yz notTop
  rw [greenQ] at blueQ
  cases blueQ

theorem blue_cover (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (c : Component) :
    blueKeys t lo searches P c ⊆ leftBlueKeys t lo searches P c ∪ rightBlueKeys t lo searches P c := by
  intro x member
  obtain ⟨_, inside, colored⟩ := Finset.mem_filter.mp member
  obtain ⟨stamp, active, external, pointColor⟩ := blue_point t lo searches P x colored
  rcases external with left | right
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(x, stamp), Finset.mem_filter.mpr
      ⟨active.1, inside, left, pointColor⟩, rfl⟩
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(x, stamp), Finset.mem_filter.mpr
      ⟨active.1, inside, right, pointColor⟩, rfl⟩

/-- The blue half of Lemma 3.1 includes the special new-row top corners. -/
theorem blue_count (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (blueKeys t lo (searches ++ [searched]) P c).card ≤ 4 := by
  have cover := Finset.card_le_card (blue_cover t lo (searches ++ [searched]) P c)
  have union := Finset.card_union_le (leftBlueKeys t lo (searches ++ [searched]) P c)
    (rightBlueKeys t lo (searches ++ [searched]) P c)
  have left := left_blue_count t lo searches searched satisfied history component
  have right := right_blue_count t lo searches searched satisfied history component
  omega

end RotationBST.Geometric.GreedyASS.Potential.Counting
