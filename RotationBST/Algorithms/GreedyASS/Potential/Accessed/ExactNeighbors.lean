module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Green
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Startup
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

theorem accessed_active {P : Finset Point} {time searched x : Nat}
    (member : x ∈ greedySweep time searched P) (different : x ≠ searched) :
    ∃ stamp, Active P (x, stamp) := by
  cases recent : latest P x with
  | none => exact (different (unseen_searched member recent)).elim
  | some stamp => exact ⟨stamp, (latest_spec P x stamp).mp recent⟩

/-- Beyond an exposed left anchor, any projection toward a search on the
left must itself be left-external. A missing same-row witness would force
the anchor into the projection rectangle. -/
theorem left_projected_external {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {a p : Point}
    (anchor : LeftExternal P a) (sa : searched ≤ a.1) (ap : a.1 < p.1)
    (active : Active P p) (accessed : p.1 ∈ greedySweep time searched P) : LeftExternal P p := by
  have visible := access_visible history active accessed (by omega)
  refine ⟨active, ?_⟩
  intro z hz sameRow
  by_contra side
  have zp : z.1 < p.1 := Nat.lt_of_not_ge side
  by_cases sz : searched ≤ z.1
  · apply visible.2 z hz (by intro eq; have := congrArg Prod.fst eq; omega)
    simp only [Rectangle]
    exact ⟨(min_le_right _ _).trans sz, zp.le.trans (le_max_left _ _),
      by rw [sameRow]; exact min_le_left _ _, by rw [sameRow]; exact le_max_left _ _⟩
  · have newer : p.2 < a.2 := by
      by_contra age
      have equal := left_quadrant satisfied anchor hz (by omega) (by omega)
      have coord := congrArg Prod.fst equal
      omega
    apply visible.2 a anchor.1.1 (by intro eq; have := congrArg Prod.fst eq; omega)
    simp only [Rectangle]
    exact ⟨(min_le_right _ _).trans sa, ap.le.trans (le_max_left _ _),
      (min_le_left _ _).trans newer.le, (history a anchor.1.1).2.le.trans (le_max_right _ _)⟩

theorem right_projected_external {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {b p : Point}
    (anchor : RightExternal P b) (bs : b.1 ≤ searched) (pb : p.1 < b.1)
    (active : Active P p) (accessed : p.1 ∈ greedySweep time searched P) : RightExternal P p := by
  have visible := access_visible history active accessed (by omega)
  refine ⟨active, ?_⟩
  intro z hz sameRow
  by_contra side
  have pz : p.1 < z.1 := Nat.lt_of_not_ge side
  by_cases zs : z.1 ≤ searched
  · apply visible.2 z hz (by intro eq; have := congrArg Prod.fst eq; omega)
    simp only [Rectangle]
    exact ⟨(min_le_left _ _).trans pz.le, zs.trans (le_max_right _ _),
      by rw [sameRow]; exact min_le_left _ _, by rw [sameRow]; exact le_max_left _ _⟩
  · have newer : p.2 < b.2 := by
      by_contra age
      have equal := right_quadrant satisfied anchor hz (by omega) (by omega)
      have coord := congrArg Prod.fst equal
      omega
    apply visible.2 b anchor.1.1 (by intro eq; have := congrArg Prod.fst eq; omega)
    simp only [Rectangle]
    exact ⟨(min_le_left _ _).trans pb.le, bs.trans (le_max_right _ _),
      (min_le_left _ _).trans newer.le, (history b anchor.1.1).2.le.trans (le_max_right _ _)⟩

/-- No extra accessed key lies between either nearest external neighbor
and the old item when the projection stays on one exposed chain. -/
theorem no_inner_access {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {x a b y : Nat}
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (anchor : (searched < a ∧ ∃ ta, LeftExternal P (a, ta)) ∨
      (b < searched ∧ ∃ tb, RightExternal P (b, tb)))
    (ay : a < y) (yb : y < b) (accessed : y ∈ greedySweep time searched P) : y = x := by
  have different : y ≠ searched := by rcases anchor with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨stamp, active⟩ := accessed_active accessed different
  have external : External P (y, stamp) := by
    rcases anchor with ⟨sa, ta, ea⟩ | ⟨bs, tb, eb⟩
    · exact Or.inl (left_projected_external satisfied history ea sa.le ay active accessed)
    · exact Or.inr (right_projected_external satisfied history eb bs.le yb active accessed)
  have hy := (mem_external P y).mpr ⟨stamp, external⟩
  have ha := (left_external_spec P x a).mp left
  have hb := (right_external_spec P x b).mp right
  by_contra same
  rcases lt_or_gt_of_ne same with yx | xy
  · have := ha.2.2 y hy yx
    omega
  · have := hb.2.2 y hy xy
    omega

/-- The old external neighbors become the exact new same-row neighbors. -/
theorem exact_new_neighbors {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {x a b : Nat}
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (accessA : a ∈ greedySweep time searched P) (accessB : b ∈ greedySweep time searched P)
    (anchor : (searched < a ∧ ∃ ta, LeftExternal P (a, ta)) ∨
      (b < searched ∧ ∃ tb, RightExternal P (b, tb))) :
    leftNeighbor (P ∪ row time (greedySweep time searched P)) (x, time) = some a ∧
      rightNeighbor (P ∪ row time (greedySweep time searched P)) (x, time) = some b := by
  have ax := ((left_external_spec P x a).mp left).2.1
  have xb := ((right_external_spec P x b).mp right).2.1
  have rowKey : ∀ y, (y, time) ∈ P ∪ row time (greedySweep time searched P) →
      y ∈ greedySweep time searched P := by
    intro y hy
    rcases Finset.mem_union.mp hy with old | current
    · have := (history (y, time) old).2
      omega
    · exact ((mem_row _ _ _).mp current).1
  constructor
  · apply (left_spec _ _ a).mpr
    refine ⟨Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨accessA, rfl⟩), ax, ?_⟩
    intro y hy yx
    by_contra beyond
    have ay : a < y := Nat.lt_of_not_ge beyond
    have eq := no_inner_access satisfied history left right anchor ay (yx.trans xb) (rowKey y hy)
    omega
  · apply (right_spec _ _ b).mpr
    refine ⟨Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨accessB, rfl⟩), xb, ?_⟩
    intro y hy xy
    by_contra beyond
    have yb : y < b := Nat.lt_of_not_ge beyond
    have eq := no_inner_access satisfied history left right anchor (ax.trans xy) yb (rowKey y hy)
    omega

/-- Exact form of Lemma 3.9. A green access becomes red and its selected
potential decreases by exactly one. -/
theorem green_exact (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .green) :
    itemColor t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red ∧
      itemAmount t lo (searches ++ [searched])
          (P ∪ row searches.length (greedySweep searches.length searched P)) x + 1 =
        itemAmount t lo (searches ++ [searched]) P x := by
  cases recent : latest P x with
  | none => simp [itemColor, recent] at old
  | some stamp =>
    have active := (latest_spec P x stamp).mp recent
    have colored : color t lo (searches ++ [searched]) P (x, stamp) = some .green := by
      simpa only [itemColor, recent] using old
    obtain ⟨external, notTop, below, valued⟩ := green_spec t lo (searches ++ [searched]) colored
    obtain ⟨a, b, left, right⟩ := green_neighbors t lo (searches ++ [searched]) colored
    have ax := ((left_external_spec P x a).mp left).2.1
    have xb := ((right_external_spec P x b).mp right).2.1
    have outside := green_search_outside t lo searches searched valid colored left right
    obtain ⟨accessA, accessB, anchor⟩ :=
      external_access_bracket satisfied history external notTop member left right outside
    obtain ⟨newLeft, newRight⟩ := exact_new_neighbors satisfied history left right accessA accessB anchor
    let keys := greedySweep searches.length searched P
    let Q := P ∪ row searches.length keys
    have newActive := top_active keys history member
    have nonexternal : ¬ External Q (x, searches.length) := by
      rintro (ext | ext)
      · have order := (top_left keys history member).mp ext a accessA
        omega
      · have order := (top_right keys history member).mp ext b accessB
        omega
    have glancing : Glancing Q (x, searches.length) :=
      Or.inl (top_glancing keys history member nonexternal).1
    change leftNeighbor Q (x, searches.length) = some a at newLeft
    change rightNeighbor Q (x, searches.length) = some b at newRight
    have redEq : red t lo Q (x, searches.length) = WithTop.some (Distance.toLCA t lo x a b) := by
      simp only [red, newLeft, newRight]
    have current : currentBlue t lo (searches ++ [searched]) x = blue t lo searched x := by
      simp [currentBlue]
    have numeric : Distance.toLCA t lo x a b + 1 ≤ blue t lo searched x := by
      simpa only [green, left, right, current, WithTop.coe_le_coe] using below
    have smaller : red t lo Q (x, searches.length) <
        WithTop.some (purple t lo (searches ++ [searched]) searches.length x) := by
      rw [redEq, purple_reset]
      exact WithTop.coe_lt_coe.mpr (by omega)
    obtain ⟨newColor, newValue⟩ := glancing_spec t lo (searches ++ [searched]) glancing
    have coloredNew : itemColor t lo (searches ++ [searched]) Q x = some .red := by
      rw [(item_spec t lo (searches ++ [searched]) newActive).1, newColor, ite_eq_left smaller]
    have amountNew : itemAmount t lo (searches ++ [searched]) Q x = Distance.toLCA t lo x a b := by
      have eq := (item_spec t lo (searches ++ [searched]) newActive).2
      rw [newValue, min_eq_left smaller.le, redEq, amount_exact] at eq
      exact WithTop.coe_inj.mp eq
    have amountOld : itemAmount t lo (searches ++ [searched]) P x = Distance.toLCA t lo x a b + 1 := by
      have eq := (item_spec t lo (searches ++ [searched]) active).2.trans valued
      rw [green, left, right, amount_exact] at eq
      exact WithTop.coe_inj.mp eq
    exact ⟨coloredNew, by rw [amountNew, amountOld]⟩

end RotationBST.Geometric.GreedyASS.Potential.Accessed
