module

public import RotationBST.Classical.RankBalanced.Insertion.Sequences
import Mathlib.Tactic

@[expose] public section

/-! Amortized rank changes of insertion: with the number of 1,1-nodes as
potential, a promotion pays for itself and the final step costs at most 7. -/
namespace RotationBST.Classical.RankBalanced

/-- `1` for a 1,1-node of rank `k` with children `l`, `r`; `0` otherwise. -/
def oneOne (l : RankedTree) (k : Int) (r : RankedTree) : Nat :=
  if k - rank l = 1 ∧ k - rank r = 1 then 1 else 0

theorem oneOne_le (l : RankedTree) (k : Int) (r : RankedTree) : oneOne l k r ≤ 1 := by
  unfold oneOne; split <;> omega

theorem oneOne_one {l : RankedTree} {k : Int} {r : RankedTree} (h1 : k - rank l = 1) (h2 : k - rank r = 1) :
    oneOne l k r = 1 := by
  unfold oneOne; simp [h1, h2]

theorem oneOne_zero {l : RankedTree} {k : Int} {r : RankedTree} (h : ¬ (k - rank l = 1 ∧ k - rank r = 1)) :
    oneOne l k r = 0 := by
  unfold oneOne; simp only [h, ↓reduceIte]

/-- The number of 1,1-nodes. -/
def phi11 : RankedTree → Nat
  | .nil => 0
  | .node l k r => oneOne l k r + phi11 l + phi11 r

theorem phi11_node (l r : RankedTree) (k : Int) :
    phi11 (.node l k r) = oneOne l k r + phi11 l + phi11 r := rfl

/-- The edit bound of an insertion into a subtree. -/
def EditBound (t t' : RankedTree) (e : Nat) : Prop :=
  (rank t' = rank t + 1 → e + phi11 t' ≤ phi11 t + 1) ∧ e + phi11 t' ≤ phi11 t + 7

theorem fixLeft_edits (l l' r : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post l l' a) (hb : EditBound l l' e) :
    EditBound (.node l k r) (fixLeft l' k r a e).1 (fixLeft l' k r a e).2.2 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vl', hrk, hgrow, ha, hga, hne⟩ := hp
  obtain ⟨bg, bn⟩ := hb
  have gr := rank_ge .wavl r vr
  have o0 := oneOne_le l k r
  unfold EditBound
  simp only [phi11_node, rank_node]
  by_cases h0 : k - rank l' = 0
  · have hg : rank l' = rank l + 1 := by omega
    have bg' := bg hg
    by_cases h1 : k - rank r = 1
    · -- Promotion: the parent was 1,1 and becomes 1,2.
      simp only [fixLeft, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
      have := oneOne_one (l := l) (k := k) (r := r) (by omega) h1
      have := oneOne_zero (l := l') (k := k + 1) (r := r) (by omega)
      omega
    · have hr2 : k - rank r = 2 := by omega
      have := oneOne_zero (l := l) (k := k) (r := r) (by omega)
      cases l' with
      | nil => exact absurd rfl hne
      | node x kx y =>
        simp only [rank_node] at h0 hg
        obtain ⟨_, ⟨_, _, _⟩, vx, vy⟩ := vl'
        have gy := rank_ge .wavl y vy
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        simp only [phi11_node] at bg'
        by_cases hx1 : kx - rank x = 1
        · simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
          have := oneOne_le x kx (.node y (k - 1) r)
          have := oneOne_le y (k - 1) r
          exact ⟨fun h => by omega, by omega⟩
        · cases y with
          | nil => simp only [rank_nil] at hot; omega
          | node y₁ ky y₂ =>
            simp only [rank_node] at hot gy
            simp only [phi11_node] at bg'
            simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
            have := oneOne_le (.node x (k - 1) y₁) k (.node y₂ (k - 1) r)
            have := oneOne_le x (k - 1) y₁
            have := oneOne_le y₂ (k - 1) r
            exact ⟨fun h => by omega, by omega⟩
  · simp only [fixLeft, h0, ne_eq, not_false_eq_true, ↓reduceIte, phi11_node, rank_node]
    have := oneOne_le l' k r
    refine ⟨fun h => by omega, ?_⟩
    rcases hrk with h | h
    · have : oneOne l' k r = oneOne l k r := by unfold oneOne; rw [h]
      omega
    · have := bg h; omega

theorem fixRight_edits (l r r' : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post r r' a) (hb : EditBound r r' e) :
    EditBound (.node l k r) (fixRight l k r' a e).1 (fixRight l k r' a e).2.2 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vr', hrk, hgrow, ha, hga, hne⟩ := hp
  obtain ⟨bg, bn⟩ := hb
  have gl := rank_ge .wavl l vl
  have o0 := oneOne_le l k r
  unfold EditBound
  simp only [phi11_node, rank_node]
  by_cases h0 : k - rank r' = 0
  · have hg : rank r' = rank r + 1 := by omega
    have bg' := bg hg
    by_cases h1 : k - rank l = 1
    · simp only [fixRight, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
      have := oneOne_one (l := l) (k := k) (r := r) h1 (by omega)
      have := oneOne_zero (l := l) (k := k + 1) (r := r') (by omega)
      omega
    · have hl2 : k - rank l = 2 := by omega
      have := oneOne_zero (l := l) (k := k) (r := r) (by omega)
      cases r' with
      | nil => exact absurd rfl hne
      | node y ky z =>
        simp only [rank_node] at h0 hg
        obtain ⟨_, ⟨_, _, _⟩, vy, vz⟩ := vr'
        have gy := rank_ge .wavl y vy
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        simp only [phi11_node] at bg'
        by_cases hz1 : ky - rank z = 1
        · simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
          have := oneOne_le (.node l (k - 1) y) ky z
          have := oneOne_le l (k - 1) y
          exact ⟨fun h => by omega, by omega⟩
        · cases y with
          | nil => simp only [rank_nil] at hot; omega
          | node y₁ kyy y₂ =>
            simp only [rank_node] at hot gy
            simp only [phi11_node] at bg'
            simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false, ↓reduceIte, phi11_node]
            have := oneOne_le (.node l (k - 1) y₁) k (.node y₂ (k - 1) z)
            have := oneOne_le l (k - 1) y₁
            have := oneOne_le y₂ (k - 1) z
            exact ⟨fun h => by omega, by omega⟩
  · simp only [fixRight, h0, ne_eq, not_false_eq_true, ↓reduceIte, phi11_node, rank_node]
    have := oneOne_le l k r'
    refine ⟨fun h => by omega, ?_⟩
    rcases hrk with h | h
    · have : oneOne l k r' = oneOne l k r := by unfold oneOne; rw [h]
      omega
    · have := bg h; omega

theorem insert_edits (t : RankedTree) (g : Nat) (hv : Valid .wavl t) :
    EditBound t (insert t g).1 (insert t g).2.2 := by
  induction t generalizing g with
  | nil => simp [EditBound, insert, phi11, oneOne, rank]
  | node l k r il ir =>
    simp only [insert]
    split
    · exact fixLeft_edits l _ r k _ _ hv (insert_post l g hv.2.2.1) (il g hv.2.2.1)
    · exact fixRight_edits l r _ k _ _ hv (insert_post r _ hv.2.2.2) (ir _ hv.2.2.2)

theorem insertEdits_le (t : RankedTree) (gs : List Nat) (hv : Valid .wavl t) :
    insertEdits t gs + phi11 (insertAll t gs) ≤ phi11 t + 7 * gs.length := by
  induction gs generalizing t with
  | nil => simp [insertEdits, insertAll]
  | cons g gs ih =>
    have h1 := (insert_edits t g hv).2
    have h2 := ih _ (insert_wavl t g hv)
    simp only [insertEdits, insertAll, List.length_cons] at h2 ⊢
    omega

/-- **Amortized rank changes**: `m` insertions into the empty tree change at
most `7m` ranks in total. -/
theorem insertEdits_empty (gs : List Nat) : insertEdits .nil gs ≤ 7 * gs.length := by
  have := insertEdits_le .nil gs trivial
  simp [phi11] at this; omega

end RotationBST.Classical.RankBalanced
