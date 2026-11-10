module

public import RotationBST.Classical.RankBalanced.Insertion.Certificate
public import RotationBST.Classical.RankBalanced.Heights
import Mathlib.Tactic

@[expose] public section

/-! Insertion keeps the WAVL rule and the AVL rule, and uses at most two
rotations. A subtree whose rank grew is a new leaf or a 1,2-node. -/
namespace RotationBST.Classical.RankBalanced

/-- A 1,2-node. -/
def OneTwo : RankedTree → Prop
  | .nil => False
  | .node a k b => (k - rank a = 1 ∧ k - rank b = 2) ∨ (k - rank a = 2 ∧ k - rank b = 1)

/-- No node is 2,2. -/
def NoTwoTwo : RankedTree → Prop
  | .nil => True
  | .node l k r => ¬ (k - rank l = 2 ∧ k - rank r = 2) ∧ NoTwoTwo l ∧ NoTwoTwo r

theorem avl_iff (t : RankedTree) : Valid .avl t ↔ Valid .wavl t ∧ NoTwoTwo t := by
  induction t with
  | nil => simp [Valid, NoTwoTwo]
  | node l k r il ir =>
    simp only [Valid, NoTwoTwo, Rule.Local, il, ir]
    constructor
    · rintro ⟨hk, hloc, ⟨wl, nl⟩, ⟨wr, nr⟩⟩
      refine ⟨⟨hk, ⟨by omega, by omega, fun h1 h2 => ?_⟩, wl, wr⟩, by omega, nl, nr⟩
      subst h1; subst h2; simp only [rank_nil] at hloc; omega
    · rintro ⟨⟨hk, ⟨dl, dr, _⟩, wl, wr⟩, n, nl, nr⟩
      exact ⟨hk, by omega, ⟨wl, nl⟩, ⟨wr, nr⟩⟩

/-- What insertion guarantees about a subtree `t'` that replaced `t`. -/
def Post (t t' : RankedTree) (a : Nat) : Prop :=
  Valid .wavl t' ∧ (rank t' = rank t ∨ rank t' = rank t + 1) ∧
    (rank t' = rank t + 1 → t' = .node .nil 0 .nil ∨ OneTwo t') ∧
    a ≤ 2 ∧ (rank t' = rank t + 1 → a = 0) ∧ t' ≠ .nil

theorem fixLeft_post (l l' r : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post l l' a) :
    Post (.node l k r) (fixLeft l' k r a e).1 (fixLeft l' k r a e).2.1 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vl', hrk, hgrow, ha, hga, hne⟩ := hp
  have gr := rank_ge .wavl r vr
  by_cases h0 : k - rank l' = 0
  · have hg : rank l' = rank l + 1 := by omega
    have ha0 := hga hg
    by_cases h1 : k - rank r = 1
    · simp only [fixLeft, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte]
      refine ⟨⟨by omega, ⟨by omega, by omega, fun h _ => absurd h hne⟩, vl', vr⟩, by simp, fun _ => ?_,
        by omega, fun _ => ha0, by simp⟩
      right; simp only [OneTwo]; left; omega
    · have hr2 : k - rank r = 2 := by omega
      cases l' with
      | nil => exact absurd rfl hne
      | node x kx y =>
        simp only [rank_node] at h0 hg
        obtain ⟨hkx, ⟨dx, dy, _⟩, vx, vy⟩ := vl'
        have gy := rank_ge .wavl y vy
        have gx := rank_ge .wavl x vx
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        by_cases hx1 : kx - rank x = 1
        · have hy2 : kx - rank y = 2 := by omega
          simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false, ↓reduceIte]
          refine ⟨⟨by omega, ⟨Or.inl hx1, by simp only [rank_node]; omega, fun _ h => by simp at h⟩, vx,
            ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, vy, vr⟩⟩, by simp; omega, by simp; omega,
            by omega, by simp; omega, by simp⟩
          subst h1; subst h2; simp only [rank_nil] at hy2 hr2; omega
        · have hx2 : kx - rank x = 2 := by omega
          have hy1 : kx - rank y = 1 := by omega
          cases y with
          | nil => simp only [rank_nil] at hy1; omega
          | node y₁ ky y₂ =>
            obtain ⟨hky, ⟨d1, d2, _⟩, v1, v2⟩ := vy
            simp only [rank_node] at hy1 gy
            simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false,
              ↓reduceIte]
            refine ⟨⟨hk, ⟨by simp only [rank_node]; omega, by simp only [rank_node]; omega,
                fun h _ => by simp at h⟩,
              ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, vx, v1⟩,
              ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, v2, vr⟩⟩,
              by simp, by simp, by simp; omega, by simp, by simp⟩
            · subst h1; simp only [rank_nil] at hx2; omega
            · subst h2; simp only [rank_nil] at hr2; omega
  · simp only [fixLeft, h0, ne_eq, not_false_eq_true, ↓reduceIte]
    refine ⟨⟨hk, ⟨by omega, dr, fun h _ => absurd h hne⟩, vl', vr⟩, by simp, by simp, ha, by simp, by simp⟩

theorem fixRight_post (l r r' : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post r r' a) :
    Post (.node l k r) (fixRight l k r' a e).1 (fixRight l k r' a e).2.1 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vr', hrk, hgrow, ha, hga, hne⟩ := hp
  have gl := rank_ge .wavl l vl
  by_cases h0 : k - rank r' = 0
  · have hg : rank r' = rank r + 1 := by omega
    have ha0 := hga hg
    by_cases h1 : k - rank l = 1
    · simp only [fixRight, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte]
      refine ⟨⟨by omega, ⟨by omega, by omega, fun _ h => absurd h hne⟩, vl, vr'⟩, by simp, fun _ => ?_,
        by omega, fun _ => ha0, by simp⟩
      right; simp only [OneTwo]; right; omega
    · have hl2 : k - rank l = 2 := by omega
      cases r' with
      | nil => exact absurd rfl hne
      | node y ky z =>
        simp only [rank_node] at h0 hg
        obtain ⟨hky, ⟨dy, dz, _⟩, vy, vz⟩ := vr'
        have gy := rank_ge .wavl y vy
        have gz := rank_ge .wavl z vz
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        by_cases hz1 : ky - rank z = 1
        · have hy2 : ky - rank y = 2 := by omega
          simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false, ↓reduceIte]
          refine ⟨⟨by omega, ⟨by simp only [rank_node]; omega, Or.inl hz1, fun h _ => by simp at h⟩,
            ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, vl, vy⟩, vz⟩, by simp; omega, by simp; omega,
            by omega, by simp; omega, by simp⟩
          subst h1; subst h2; simp only [rank_nil] at hy2 hl2; omega
        · have hz2 : ky - rank z = 2 := by omega
          have hy1 : ky - rank y = 1 := by omega
          cases y with
          | nil => simp only [rank_nil] at hy1; omega
          | node y₁ kyy y₂ =>
            obtain ⟨hkyy, ⟨d1, d2, _⟩, v1, v2⟩ := vy
            simp only [rank_node] at hy1 gy
            simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false,
              ↓reduceIte]
            refine ⟨⟨hk, ⟨by simp only [rank_node]; omega, by simp only [rank_node]; omega,
                fun h _ => by simp at h⟩,
              ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, vl, v1⟩,
              ⟨by omega, ⟨by omega, by omega, fun h1 h2 => ?_⟩, v2, vz⟩⟩,
              by simp, by simp, by simp; omega, by simp, by simp⟩
            · subst h1; simp only [rank_nil] at hl2; omega
            · subst h2; simp only [rank_nil] at hz2; omega
  · simp only [fixRight, h0, ne_eq, not_false_eq_true, ↓reduceIte]
    refine ⟨⟨hk, ⟨dl, by omega, fun _ h => absurd h hne⟩, vl, vr'⟩, by simp, by simp, ha, by simp, by simp⟩

theorem insert_post (t : RankedTree) (g : Nat) (hv : Valid .wavl t) :
    Post t (insert t g).1 (insert t g).2.1 := by
  induction t generalizing g with
  | nil =>
    refine ⟨⟨le_rfl, ⟨by simp, by simp, fun _ _ => rfl⟩, trivial, trivial⟩, by simp [insert], ?_,
      by simp [insert], by simp [insert], by simp [insert]⟩
    intro _; left; rfl
  | node l k r il ir =>
    simp only [insert]
    split
    · exact fixLeft_post l _ r k _ _ hv (il g hv.2.2.1)
    · exact fixRight_post l r _ k _ _ hv (ir _ hv.2.2.2)

/-! ### No 2,2-nodes: the AVL rule -/

theorem fixLeft_noTwoTwo (l l' r : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post l l' a) (n : NoTwoTwo (.node l k r)) (n' : NoTwoTwo l') :
    NoTwoTwo (fixLeft l' k r a e).1 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vl', hrk, hgrow, ha, hga, hne⟩ := hp
  obtain ⟨n0, nl, nr⟩ := n
  have gr := rank_ge .wavl r vr
  by_cases h0 : k - rank l' = 0
  · have hg : rank l' = rank l + 1 := by omega
    by_cases h1 : k - rank r = 1
    · simp only [fixLeft, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte]
      exact ⟨by omega, n', nr⟩
    · cases l' with
      | nil => exact absurd rfl hne
      | node x kx y =>
        simp only [rank_node] at h0 hg
        obtain ⟨nx0, nx, ny⟩ := n'
        obtain ⟨_, ⟨_, _, _⟩, vx, vy⟩ := vl'
        have gx := rank_ge .wavl x vx
        have gy := rank_ge .wavl y vy
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        by_cases hx1 : kx - rank x = 1
        · simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false, ↓reduceIte]
          exact ⟨by simp only [rank_node]; omega, nx, ⟨by omega, ny, nr⟩⟩
        · cases y with
          | nil => simp only [rank_nil] at hot; omega
          | node y₁ ky y₂ =>
            simp only [rank_node] at hot
            obtain ⟨_, ny1, ny2⟩ := ny
            simp only [fixLeft, rank_node, h0, h1, hx1, ne_eq, not_true_eq_false, ↓reduceIte]
            exact ⟨by simp only [rank_node]; omega, ⟨by omega, nx, ny1⟩, ⟨by omega, ny2, nr⟩⟩
  · simp only [fixLeft, h0, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ⟨by omega, n', nr⟩

theorem fixRight_noTwoTwo (l r r' : RankedTree) (k : Int) (a e : Nat)
    (hv : Valid .wavl (.node l k r)) (hp : Post r r' a) (n : NoTwoTwo (.node l k r)) (n' : NoTwoTwo r') :
    NoTwoTwo (fixRight l k r' a e).1 := by
  obtain ⟨hk, ⟨dl, dr, _⟩, vl, vr⟩ := hv
  obtain ⟨vr', hrk, hgrow, ha, hga, hne⟩ := hp
  obtain ⟨n0, nl, nr⟩ := n
  have gl := rank_ge .wavl l vl
  by_cases h0 : k - rank r' = 0
  · have hg : rank r' = rank r + 1 := by omega
    by_cases h1 : k - rank l = 1
    · simp only [fixRight, h0, h1, ne_eq, not_true_eq_false, ↓reduceIte]
      exact ⟨by omega, nl, n'⟩
    · cases r' with
      | nil => exact absurd rfl hne
      | node y ky z =>
        simp only [rank_node] at h0 hg
        obtain ⟨ny0, ny, nz⟩ := n'
        obtain ⟨_, ⟨_, _, _⟩, vy, vz⟩ := vr'
        have gy := rank_ge .wavl y vy
        have gz := rank_ge .wavl z vz
        rcases hgrow (by simpa using hg) with hleaf | hot
        · simp at hleaf; omega
        simp only [OneTwo] at hot
        by_cases hz1 : ky - rank z = 1
        · simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false, ↓reduceIte]
          exact ⟨by simp only [rank_node]; omega, ⟨by omega, nl, ny⟩, nz⟩
        · cases y with
          | nil => simp only [rank_nil] at hot; omega
          | node y₁ kyy y₂ =>
            simp only [rank_node] at hot
            obtain ⟨_, ny1, ny2⟩ := ny
            simp only [fixRight, rank_node, h0, h1, hz1, ne_eq, not_true_eq_false, ↓reduceIte]
            exact ⟨by simp only [rank_node]; omega, ⟨by omega, nl, ny1⟩, ⟨by omega, ny2, nz⟩⟩
  · simp only [fixRight, h0, ne_eq, not_false_eq_true, ↓reduceIte]
    exact ⟨by omega, nl, n'⟩

theorem insert_noTwoTwo (t : RankedTree) (g : Nat) (hv : Valid .wavl t) (n : NoTwoTwo t) :
    NoTwoTwo (insert t g).1 := by
  induction t generalizing g with
  | nil => simp [insert, NoTwoTwo, rank]
  | node l k r il ir =>
    simp only [insert]
    split
    · exact fixLeft_noTwoTwo l _ r k _ _ hv (insert_post l g hv.2.2.1) n (il g hv.2.2.1 n.2.1)
    · exact fixRight_noTwoTwo l r _ k _ _ hv (insert_post r _ hv.2.2.2) n (ir _ hv.2.2.2 n.2.2)

theorem insert_wavl (t : RankedTree) (g : Nat) (hv : Valid .wavl t) : Valid .wavl (insert t g).1 :=
  (insert_post t g hv).1

theorem insert_avl (t : RankedTree) (g : Nat) (hv : Valid .avl t) : Valid .avl (insert t g).1 := by
  rw [avl_iff] at hv ⊢
  exact ⟨insert_wavl t g hv.1, insert_noTwoTwo t g hv.1 hv.2⟩

theorem insert_rotations (t : RankedTree) (g : Nat) (hv : Valid .wavl t) : (insert t g).2.1 ≤ 2 :=
  (insert_post t g hv).2.2.2.1

end RotationBST.Classical.RankBalanced
