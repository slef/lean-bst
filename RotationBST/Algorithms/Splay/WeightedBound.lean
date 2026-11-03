module

public import RotationBST.Algorithms.Splay.AccessLemma
public import RotationBST.Models.Rotation.Existence.Abstract

@[expose] public section

namespace RotationBST.Splay

variable {s t : Tree} {xs : List Nat} {k lo : Nat}

noncomputable def weightedSum (w : Nat → ℝ) (total : ℝ) : List Nat → ℝ
  | [] => 0
  | x :: xs => 1 + 3 * (Real.logb 2 total - Real.logb 2 (w x)) + weightedSum w total xs

/-- The access lemma telescopes for any fixed positive weights. -/
theorem weighted_run (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (past : List Nat) (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((algorithm.runFrom past t xs).2 : ℝ) + potential w (algorithm.runFrom past t xs).1 0 -
      potential w t 0 ≤ weightedSum w (mass w t 0) xs := by
  induction xs generalizing past t with
  | nil => simp [Algorithm.runFrom, weightedSum]
  | cons x xs ih =>
      have hx := valid x (by simp)
      have ha := (run_correct t x hx).1
      have hb := access_lemma w hw t x hx
      rcases he : run t x with ⟨u, k⟩
      rw [he] at ha hb
      have hv : ∀ y ∈ xs, y < u.size := by
        intro y hy
        rw [← ha.1.size_eq]
        exact valid y (by simp [hy])
      have hi := ih (past ++ [x]) u hv
      have hm := mass_rotations w ha.1 0
      rw [← hm] at hi
      rcases hf : algorithm.runFrom (past ++ [x]) u xs with ⟨v, m⟩
      rw [hf] at hi
      have he' : algorithm.step past t x = (u, k) := he
      simp only [Algorithm.runFrom, he', hf, weightedSum, Nat.cast_add]
      dsimp only at hi hb ⊢
      linarith

/-- Uniform node-weight bounds give explicit bounds on the tree potential. -/
theorem potential_bounds (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (lower upper : ℝ) (hlower : 0 < lower) (hwlower : ∀ i, lower ≤ w i)
    (t : Tree) (lo : Nat) (hupper : mass w t lo ≤ upper) :
    (t.size : ℝ) * Real.logb 2 lower ≤ potential w t lo ∧
      potential w t lo ≤ (t.size : ℝ) * Real.logb 2 upper := by
  induction t generalizing lo with
  | nil => simp [Tree.size, potential]
  | node l r il ir =>
      obtain ⟨hll, hlu⟩ := il lo ((mass_left_le w hw l r lo).trans hupper)
      obtain ⟨hrl, hru⟩ := ir (lo + l.size + 1) ((mass_right_le w hw l r lo).trans hupper)
      have hml := (hwlower (lo + l.size)).trans (weight_le_mass w hw l r lo)
      have hlogl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hlower hml
      have hlogu := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (mass_pos w hw l r lo) hupper
      simp only [Tree.size, potential, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith

theorem execution_mass_eq (w : Nat → ℝ) (h : Execution s xs t k) :
    mass w s lo = mass w t lo := by
  induction h with
  | nil => rfl
  | cons ha _ ih => exact (mass_rotations w ha.1 lo).trans ih

/-- A quantitative fixed-weight bound, including the initial-tree allowance. -/
theorem weighted_bound (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (lower : ℝ) (hlower : 0 < lower) (hwlower : ∀ i, lower ≤ w i)
    (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.cost t xs : ℝ) ≤ weightedSum w (mass w t 0) xs +
      (t.size : ℝ) * (Real.logb 2 (mass w t 0) - Real.logb 2 lower) := by
  have hb := weighted_run w hw [] t xs valid
  have he := algorithm.execution [] t xs valid
  have hs := he.size_eq.symm
  have hmass := (execution_mass_eq w he (lo := 0)).symm
  have hi := (potential_bounds w hw lower (mass w t 0) hlower hwlower t 0 le_rfl).2
  have hf := (potential_bounds w hw lower (mass w t 0) hlower hwlower
    (algorithm.runFrom [] t xs).1 0 (le_of_eq hmass)).1
  rw [hs] at hf
  unfold Algorithm.cost
  nlinarith

theorem mass_unit (t : Tree) (lo : Nat) : mass (fun _ => 1) t lo = t.size := by
  induction t generalizing lo with
  | nil => simp [mass, Tree.size]
  | node l r il ir => simp [mass, Tree.size, il, ir, Nat.cast_add, Nat.cast_one]

theorem weightedSum_unit (total : ℝ) (xs : List Nat) :
    weightedSum (fun _ => 1) total xs = (xs.length : ℝ) * (1 + 3 * Real.logb 2 total) := by
  induction xs with
  | nil => simp [weightedSum]
  | cons x xs ih => simp only [weightedSum, Real.logb_one, sub_zero, ih,
      List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- The balance theorem with explicit constants and arbitrary initial shape. -/
theorem balance (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.totalCost t xs : ℝ) ≤
      (xs.length : ℝ) * (2 + 3 * Real.logb 2 t.size) + (t.size : ℝ) * Real.logb 2 t.size := by
  have h := weighted_bound (fun _ => 1) (by intro; norm_num) 1 (by norm_num)
    (by intro; rfl) t xs valid
  simp only [mass_unit, weightedSum_unit, Real.logb_one, sub_zero] at h
  simp only [Algorithm.totalCost, Nat.cast_add]
  nlinarith

end RotationBST.Splay
