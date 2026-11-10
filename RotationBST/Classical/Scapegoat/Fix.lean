module

public import RotationBST.Classical.Scapegoat.Shape
public import RotationBST.Classical.WeightBalanced.Rebuild
import Mathlib.Tactic

@[expose] public section

/-! Partial rebuilding: `fix` is a rotation sequence that keeps every depth
within any bound met by the new leaf's parent, and pays for its rotations by
the drop of the imbalance potential. -/
namespace RotationBST.Classical.Scapegoat
open WeightBalanced Static Dictionary

variable {α : ℚ}

/-! ### Rebuilding and the balanced tree -/

theorem phi_balanced (n : Nat) : phi (balanced n) = 0 := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [balanced, phi]
    | succ n =>
      rw [balanced, phi, ih _ (by omega), ih _ (by omega), balanced_size, balanced_size]
      simp only [imb]; omega

theorem phi_rebuild (t : Tree) : phi (rebuild t).1 = 0 := phi_balanced _

theorem rebuild_size (t : Tree) : (rebuild t).1.size = t.size := balanced_size _

/-- A violation makes the subtree's height too large for its size. -/
theorem violates_log2 (hα : 1 / 2 ≤ α) {t : Tree} {k : Nat} (h : Violates α t k) (hs : 0 < t.size) :
    Nat.log2 t.size < t.depth k := by
  unfold Violates at h
  have hp : (1 / 2 : ℚ) ^ t.depth k ≤ α ^ t.depth k := pow_le_pow_left₀ (by norm_num) hα _
  have h2 : (t.size : ℚ) < 2 ^ t.depth k := by
    have : (1 / 2 : ℚ) ^ t.depth k * t.size < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hp (by positivity)) h
    rw [div_pow, one_pow, one_div, inv_mul_lt_iff₀ (by positivity), mul_one] at this
    exact this
  exact (Nat.log2_lt (by omega)).mpr (by exact_mod_cast h2)

theorem not_violates_root {t : Tree} {k : Nat} (hk : k < t.size) (h0 : t.depth k = 0) :
    ¬ Violates α t k := by
  unfold Violates; rw [h0, pow_zero, one_mul]
  exact not_lt.mpr (by exact_mod_cast (show 1 ≤ t.size by omega))

/-! ### Unfolding `fix` -/

theorem fix_node (l r : Tree) (k : Nat) :
    fix α (.node l r) k =
      match (if k < l.size then (fix α l k).map fun p => (Tree.node p.1 r, p.2)
          else if k = l.size then none
          else (fix α r (k - l.size - 1)).map fun p => (Tree.node l p.1, p.2)) with
      | some p => some p
      | none => if Violates α (.node l r) k then some (rebuild (.node l r)) else none := by
  rw [fix]; rfl

theorem fix_none (t : Tree) (k : Nat) (hk : k < t.size) (h : fix α t k = none) : ¬ Violates α t k := by
  cases t with
  | nil => simp [Tree.size] at hk
  | node l r =>
    rw [fix_node] at h
    intro hv
    split at h
    · simp at h
    · simp [hv] at h

/-- The three ways `fix` can succeed on a node. -/
theorem fix_some (l r : Tree) (k : Nat) (p : Tree × Nat) (h : fix α (.node l r) k = some p) :
    (k < l.size ∧ ∃ q, fix α l k = some q ∧ p = (.node q.1 r, q.2)) ∨
    (l.size < k ∧ ∃ q, fix α r (k - l.size - 1) = some q ∧ p = (.node l q.1, q.2)) ∨
    (Violates α (.node l r) k ∧ p = rebuild (.node l r) ∧
      (k < l.size → fix α l k = none) ∧ (l.size < k → fix α r (k - l.size - 1) = none)) := by
  rw [fix_node] at h
  by_cases h1 : k < l.size
  · simp only [h1, ↓reduceIte] at h
    cases hl : fix α l k with
    | some q =>
      rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨h1, q, rfl, h.symm⟩
    | none =>
      rw [hl] at h; simp only [Option.map_none] at h
      by_cases hv : Violates α (.node l r) k
      · simp only [hv, ↓reduceIte, Option.some.injEq] at h
        exact Or.inr (Or.inr ⟨hv, h.symm, fun _ => rfl, fun h' => absurd h' (by omega)⟩)
      · simp [hv] at h
  · by_cases h2 : k = l.size
    · have hv0 := not_violates_root (α := α) (t := .node l r) (k := k)
        (by simp [Tree.size]; omega) (depth_root h2)
      subst h2
      simp [hv0] at h
    · simp only [h1, h2, ↓reduceIte] at h
      cases hr : fix α r (k - l.size - 1) with
      | some q =>
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨by omega, q, rfl, h.symm⟩)
      | none =>
        rw [hr] at h; simp only [Option.map_none] at h
        by_cases hv : Violates α (.node l r) k
        · simp only [hv, ↓reduceIte, Option.some.injEq] at h
          exact Or.inr (Or.inr ⟨hv, h.symm, fun h' => absurd h' h1, fun _ => rfl⟩)
        · simp [hv] at h

/-! ### Certificates -/

theorem fix_spec (t : Tree) (k : Nat) (p : Tree × Nat) (h : fix α t k = some p) :
    Rotations t p.1 p.2 ∧ p.1.size = t.size := by
  induction t generalizing k p with
  | nil => simp [fix] at h
  | node l r il ir =>
    rcases fix_some l r k p h with ⟨_, q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩ | ⟨_, rfl, _, _⟩
    · obtain ⟨hr, hs⟩ := il k q hq
      exact ⟨hr.inLeft, by simp only [Tree.size, hs]⟩
    · obtain ⟨hr, hs⟩ := ir _ q hq
      exact ⟨hr.inRight, by simp only [Tree.size, hs]⟩
    · exact ⟨rebuild_rotations _, rebuild_size _⟩

/-- Every depth of the result satisfies any downward-closed condition `P`
that the other keys meet and that the new key's parent meets. The offset `j`
is the depth of the subtree. -/
theorem fix_depth (hα : 1 / 2 ≤ α) (P : Nat → Prop) (anti : ∀ a b, a ≤ b → P b → P a)
    (t : Tree) (k j : Nat) (p : Tree × Nat) (hk : k < t.size) (h : fix α t k = some p)
    (hrest : ∀ z < t.size, z ≠ k → P (j + t.depth z)) (hpar : P (j + t.depth k - 1)) :
    ∀ z < p.1.size, P (j + p.1.depth z) := by
  induction t generalizing k j p with
  | nil => simp [fix] at h
  | node l r il ir =>
    rcases fix_some l r k p h with ⟨h1, q, hq, rfl⟩ | ⟨h1, q, hq, rfl⟩ | ⟨hv, rfl, _, _⟩
    · have hs := (fix_spec l k q hq).2
      have ih := il k (j + 1) q h1 hq
        (fun z hz hzk => by
          have := hrest z (by simp [Tree.size]; omega) hzk
          rw [depth_left hz] at this
          rwa [show j + 1 + l.depth z = j + (l.depth z + 1) by omega])
        (by
          rw [depth_left h1] at hpar
          rwa [show j + 1 + l.depth k - 1 = j + (l.depth k + 1) - 1 by omega])
      intro z hz
      simp only [Tree.size, hs] at hz
      by_cases z1 : z < l.size
      · rw [depth_left (by omega)]
        have := ih z (by omega)
        rwa [show j + (q.1.depth z + 1) = j + 1 + q.1.depth z by omega]
      · by_cases z2 : z = l.size
        · have := hrest z (by simp [Tree.size]; omega) (by omega)
          rw [depth_root z2] at this
          rwa [depth_root (by omega)]
        · have := hrest z (by simp [Tree.size]; omega) (by omega)
          rw [depth_right (by omega)] at this
          rwa [depth_right (by omega), hs]
    · have hs := (fix_spec r _ q hq).2
      have ih := ir (k - l.size - 1) (j + 1) q (by simp [Tree.size] at hk; omega) hq
        (fun z hz hzk => by
          have := hrest (l.size + 1 + z) (by simp [Tree.size]; omega) (by omega)
          rw [depth_right (by omega), show l.size + 1 + z - l.size - 1 = z by omega] at this
          rwa [show j + 1 + r.depth z = j + (r.depth z + 1) by omega])
        (by
          rw [depth_right h1] at hpar
          rwa [show j + 1 + r.depth (k - l.size - 1) - 1 = j + (r.depth (k - l.size - 1) + 1) - 1 by omega])
      intro z hz
      simp only [Tree.size, hs] at hz
      by_cases z1 : z < l.size
      · have := hrest z (by simp [Tree.size]; omega) (by omega)
        rw [depth_left z1] at this
        rwa [depth_left z1]
      · by_cases z2 : z = l.size
        · have := hrest z (by simp [Tree.size]; omega) (by omega)
          rw [depth_root z2] at this
          rwa [depth_root z2]
        · have := ih (z - l.size - 1) (by omega)
          rw [depth_right (by omega)]
          rwa [show j + (q.1.depth (z - l.size - 1) + 1) = j + 1 + q.1.depth (z - l.size - 1) by omega]
    · -- Rebuilt: depths at most `log₂ s < depth k`.
      have hlog := violates_log2 hα hv (by simp [Tree.size])
      intro z hz
      rw [rebuild_size] at hz
      have hd := balanced_depth _ z hz
      exact anti _ _ (by simp only [rebuild]; omega) hpar

/-- The rotations of `fix` are paid by the drop of `Φ`. -/
theorem fix_phi (hα : 1 / 2 < α) (t : Tree) (k : Nat) (p : Tree × Nat) (hk : k < t.size)
    (h : fix α t k = some p) :
    (2 * α - 1) * p.2 ≤ 2 * ((phi t : ℚ) - phi p.1) ∧ phi p.1 ≤ phi t := by
  induction t generalizing k p with
  | nil => simp [fix] at h
  | node l r il ir =>
    rcases fix_some l r k p h with ⟨h1, q, hq, rfl⟩ | ⟨h1, q, hq, rfl⟩ | ⟨hv, rfl, hnl, hnr⟩
    · have hs := (fix_spec l k q hq).2
      obtain ⟨a, b⟩ := il k q h1 hq
      simp only [phi, hs]; push_cast; constructor <;> [linarith; omega]
    · have hs := (fix_spec r _ q hq).2
      obtain ⟨a, b⟩ := ir _ q (by simp [Tree.size] at hk; omega) hq
      simp only [phi, hs]; push_cast; constructor <;> [linarith; omega]
    · refine ⟨?_, by rw [phi_rebuild]; omega⟩
      rw [phi_rebuild]
      have hc := rebuild_cost (.node l r)
      have h2α : (0 : ℚ) ≤ 2 * α - 1 := by linarith
      -- The child on the search path holds more than an `α` fraction of the keys.
      have heavy : ∃ c o : Nat, (c = l.size ∧ o = r.size ∨ c = r.size ∧ o = l.size) ∧
          α * (l.size + 1 + r.size : Nat) < c := by
        unfold Violates at hv
        by_cases h1 : k < l.size
        · have hn := fix_none l k h1 (hnl h1)
          unfold Violates at hn; rw [not_lt] at hn
          rw [depth_left h1, pow_succ] at hv
          refine ⟨l.size, r.size, Or.inl ⟨rfl, rfl⟩, ?_⟩
          have hp : 0 < α ^ l.depth k := by positivity
          simp only [Tree.size] at hv
          nlinarith
        · by_cases h2 : k = l.size
          · exact absurd hv (not_violates_root (α := α) (by simp [Tree.size]; omega)
              (depth_root h2))
          · have h3 : l.size < k := by omega
            have hn := fix_none r _ (by simp [Tree.size] at hk; omega) (hnr h3)
            unfold Violates at hn; rw [not_lt] at hn
            rw [depth_right h3, pow_succ] at hv
            refine ⟨r.size, l.size, Or.inr ⟨rfl, rfl⟩, ?_⟩
            have hp : 0 < α ^ r.depth (k - l.size - 1) := by positivity
            simp only [Tree.size] at hv
            nlinarith
      obtain ⟨c, o, hco, hheavy⟩ := heavy
      have himb : (c : ℚ) ≤ imb l.size r.size + o + 1 := by
        have : c ≤ imb l.size r.size + o + 1 := by
          rcases hco with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [imb] <;> omega
        exact_mod_cast this
      have hsum : (c : ℚ) + o = l.size + r.size := by
        rcases hco with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
      have hphi : (imb l.size r.size : ℚ) ≤ phi (.node l r) := by
        simp only [phi]; push_cast
        have h1 : (0 : ℚ) ≤ phi l := by positivity
        have h2 : (0 : ℚ) ≤ phi r := by positivity
        linarith
      have hc' : ((rebuild (Tree.node l r)).2 : ℚ) ≤ 2 * (l.size + 1 + r.size : Nat) := by
        have := hc; simp only [Tree.size] at this; exact_mod_cast this
      push_cast at hheavy hc' ⊢
      nlinarith

end RotationBST.Classical.Scapegoat
