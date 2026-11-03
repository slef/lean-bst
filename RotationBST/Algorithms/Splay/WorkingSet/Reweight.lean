module

public import RotationBST.Algorithms.Splay.WorkingSet.WeightSum

@[expose] public section

namespace RotationBST.Splay

/-- Mass is monotone in the weights of exactly the keys in this subtree. -/
theorem mass_mono_on (w v : Nat → ℝ) (t : Tree) (lo : Nat)
    (h : ∀ i, lo ≤ i → i < lo + t.size → v i ≤ w i) : mass v t lo ≤ mass w t lo := by
  induction t generalizing lo with
  | nil => exact le_rfl
  | node l r il ir =>
      have hl := il lo (by intro i hi hi'; apply h i hi; simp only [Tree.size]; omega)
      have hr := ir (lo + l.size + 1) (by
        intro i hi hi'; apply h i (by omega); simp only [Tree.size]; omega)
      have hx := h (lo + l.size) (by omega) (by simp only [Tree.size]; omega)
      simp only [mass]
      linarith

/-- Lowering all weights in a subtree cannot increase its potential. -/
theorem potential_mono_on (w v : Nat → ℝ) (hv : ∀ i, 0 < v i) (t : Tree) (lo : Nat)
    (h : ∀ i, lo ≤ i → i < lo + t.size → v i ≤ w i) :
    potential v t lo ≤ potential w t lo := by
  induction t generalizing lo with
  | nil => exact le_rfl
  | node l r il ir =>
      have hl := il lo (by intro i hi hi'; apply h i hi; simp only [Tree.size]; omega)
      have hr := ir (lo + l.size + 1) (by
        intro i hi hi'; apply h i (by omega); simp only [Tree.size]; omega)
      have hm := mass_mono_on w v (.node l r) lo h
      have hg := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (mass_pos v hv l r lo) hm
      simp only [potential]
      linarith

/-- Increasing only the root's weight while preserving total mass does not
increase potential if every other node's weight decreases. -/
theorem potential_reweight_root (w v : Nat → ℝ) (hv : ∀ i, 0 < v i) (l r : Tree)
    (htotal : mass v (.node l r) 0 = mass w (.node l r) 0)
    (hother : ∀ i, i < (Tree.node l r).size → i ≠ l.size → v i ≤ w i) :
    potential v (.node l r) 0 ≤ potential w (.node l r) 0 := by
  have hl := potential_mono_on w v hv l 0 (by
    intro i _ hi
    apply hother i (by simp only [Tree.size]; omega) (by omega))
  have hr := potential_mono_on w v hv r (0 + l.size + 1) (by
    intro i hi hi'
    apply hother i (by simp only [Tree.size]; omega) (by omega))
  simp only [potential, htotal]
  linarith

end RotationBST.Splay

namespace RotationBST.Recency

/-- Moving the just-accessed root to the front of the recency list is free in
amortized analysis: it cannot increase the sum-of-log-masses potential. -/
theorem touch_potential (order : List Nat) (l r : Tree)
    (hp : order.Perm (List.range (Tree.node l r).size)) :
    Splay.potential (weight (touch order l.size)) (.node l r) 0 ≤
      Splay.potential (weight order) (.node l r) 0 := by
  have hx : l.size ∈ order := hp.mem_iff.mpr (by simp [Tree.size]; omega)
  apply Splay.potential_reweight_root _ _ (weight_pos _) l r
  · rw [mass_weight _ _ ((touch_perm order hx).trans hp), mass_weight _ _ hp]
  · intro i _ hne
    exact weight_touch_le order hne.symm

end RotationBST.Recency
