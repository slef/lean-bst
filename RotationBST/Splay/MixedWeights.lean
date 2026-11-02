module

public import RotationBST.WorkingSet.SplayBound

@[expose] public section

namespace RotationBST.Splay
open Recency

noncomputable def mixedWeight (fixed : Nat → ℝ) (order : List Nat) (i : Nat) : ℝ :=
  weight order i + fixed i

theorem mixedWeight_pos (fixed : Nat → ℝ) (hf : ∀ i, 0 ≤ fixed i) (order : List Nat) :
    ∀ i, 0 < mixedWeight fixed order i := by
  intro i
  exact add_pos_of_pos_of_nonneg (weight_pos order i) (hf i)

theorem mass_add (w v : Nat → ℝ) (t : Tree) (lo : Nat) :
    mass (fun i => w i + v i) t lo = mass w t lo + mass v t lo := by
  induction t generalizing lo with
  | nil => simp [mass]
  | node l r il ir => simp only [mass, il, ir]; ring

/-- Adding fixed nonnegative weights preserves the free recency reweighting step. -/
theorem mixed_touch_potential (fixed : Nat → ℝ) (hf : ∀ i, 0 ≤ fixed i)
    (order : List Nat) (l r : Tree) (hp : order.Perm (List.range (Tree.node l r).size)) :
    potential (mixedWeight fixed (touch order l.size)) (.node l r) 0 ≤
      potential (mixedWeight fixed order) (.node l r) 0 := by
  have hx : l.size ∈ order := hp.mem_iff.mpr (by simp [Tree.size]; omega)
  apply potential_reweight_root (mixedWeight fixed order) (mixedWeight fixed (touch order l.size)) (mixedWeight_pos fixed hf _) l r
  · change mass (fun i => weight (touch order l.size) i + fixed i) (.node l r) 0 =
      mass (fun i => weight order i + fixed i) (.node l r) 0
    rw [mass_add, mass_add]
    rw [mass_weight _ _ ((touch_perm order hx).trans hp), mass_weight _ _ hp]
  · intro i _ hne
    exact add_le_add_left (weight_touch_le order hne.symm) _

/-- The access lemma remains valid with a mixture of fixed and recency weights,
with the post-access recency order in its final potential. -/
theorem mixed_access (fixed : Nat → ℝ) (hf : ∀ i, 0 ≤ fixed i)
    (order : List Nat) (t : Tree) (x : Nat)
    (hp : order.Perm (List.range t.size)) (hx : x < t.size) :
    ((run t x).2 : ℝ) + potential (mixedWeight fixed (touch order x)) (run t x).1 0 -
      potential (mixedWeight fixed order) t 0 ≤
      1 + 3 * (Real.logb 2 (mass (mixedWeight fixed order) t 0) -
        Real.logb 2 (mixedWeight fixed order x)) := by
  have ha := (run_correct t x hx).1
  have hb := access_lemma _ (mixedWeight_pos fixed hf order) t x hx
  have hpot : potential (mixedWeight fixed (touch order x)) (run t x).1 0 ≤
      potential (mixedWeight fixed order) (run t x).1 0 := by
    generalize he : (run t x).1 = u at ha ⊢
    cases u with
    | nil => exact ha.2.elim
    | node l r =>
        have hroot : l.size = x := ha.2
        rw [← hroot]
        apply mixed_touch_potential fixed hf order l r
        rw [← ha.1.size_eq]
        exact hp
  linarith

end RotationBST.Splay
