module

public import RotationBST.Splay.Conditional.Algorithm.Abstract
public import RotationBST.Splay.StaticOptimality
public import RotationBST.Splay.Pointer

@[expose] public section

namespace RotationBST.Splay

theorem conditionalStep_rotations (w : Nat → ℝ) (t : Tree) (x : Nat)
    (hx : x < t.size) : Rotations t (conditionalStep w t x).1 (conditionalStep w t x).2 := by
  unfold conditionalStep
  split
  · exact (run_correct t x hx).1.1
  · exact .refl

theorem conditionalRun_rotations (w : Nat → ℝ) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Rotations t (conditionalRun w t xs).1 (conditionalRun w t xs).2 := by
  induction xs generalizing t with
  | nil => exact .refl
  | cons x xs ih =>
      have ha := conditionalStep_rotations w t x (valid x (by simp))
      have hv : ∀ y ∈ xs, y < (conditionalStep w t x).1.size := by
        intro y hy; rw [← ha.size_eq]; exact valid y (by simp [hy])
      exact ha.append (ih _ hv)

/-- Every charged rotation in a long splay drops potential by at least one half. -/
theorem conditionalStep_drop (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (x : Nat) (hx : x < t.size) :
    ((conditionalStep w t x).2 : ℝ) ≤
      2 * (potential w t 0 - potential w (conditionalStep w t x).1 0) := by
  have hb := access_lemma w hw t x hx
  unfold conditionalStep
  split
  · linarith
  · simp

/-- Restructuring cost telescopes independently of the number of requests. -/
theorem conditionalRun_drop (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((conditionalRun w t xs).2 : ℝ) ≤
      2 * (potential w t 0 - potential w (conditionalRun w t xs).1 0) := by
  induction xs generalizing t with
  | nil => simp [conditionalRun]
  | cons x xs ih =>
      have ha := conditionalStep_rotations w t x (valid x (by simp))
      have hb := conditionalStep_drop w hw t x (valid x (by simp))
      have hv : ∀ y ∈ xs, y < (conditionalStep w t x).1.size := by
        intro y hy; rw [← ha.size_eq]; exact valid y (by simp [hy])
      have hi := ih _ hv
      simp only [conditionalRun, Nat.cast_add]
      linarith

/-- Long-splay theorem, with threshold `6 log₂(W/w(x)) + 2` and explicit factor
 two. This bounds restructuring, not the cost of all the intervening searches. -/
theorem long_splay (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
    (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((conditionalRun w t xs).2 : ℝ) ≤
      2 * ∑ i ∈ Finset.range t.size, Real.logb 2 (mass w t 0 / w i) := by
  cases t with
  | nil =>
      have hx : xs = [] := by
        cases xs with
        | nil => rfl
        | cons x xs => have := valid x (by simp); simp [Tree.size] at this
      subst xs
      simp [conditionalRun, Tree.size]
  | node l r =>
      have hb := conditionalRun_drop w hw (.node l r) xs valid
      have hi := potential_upper w hw (.node l r) 0 (mass w (.node l r) 0) le_rfl
      have hf := potential_lower_weights w hw (conditionalRun w (.node l r) xs).1 0
      have he := conditionalRun_rotations w (.node l r) xs valid
      rw [← mass_rotations (fun i => Real.logb 2 (w i)) he] at hf
      have hp := mass_pos w hw l r 0
      have heq : (∑ i ∈ Finset.range (Tree.node l r).size, Real.logb 2 (mass w (.node l r) 0 / w i)) =
          ((Tree.node l r).size : ℝ) * Real.logb 2 (mass w (.node l r) 0) -
            mass (fun i => Real.logb 2 (w i)) (.node l r) 0 := by
        simp_rw [Real.logb_div hp.ne' (hw _).ne']
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mass_eq_finset]
      rw [heq]
      linarith

/-- With unit weights, total restructuring over arbitrarily many conditional
searches is at most `2 n log₂ n`. -/
theorem long_splay_unit (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((conditionalRun (fun _ => 1) t xs).2 : ℝ) ≤ 2 * (t.size : ℝ) * Real.logb 2 t.size := by
  have h := long_splay (fun _ => 1) (by intro; norm_num) t xs valid
  simpa only [mass_unit, div_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc] using h

/-- A short conditional search still visits its requested node; it is not
misrepresented as a zero-cost root access. -/
theorem conditionalStep_pointer (w : Nat → ℝ) (t : Tree) (x : Nat) (hx : x < t.size) :
    ∃ k, k ≤ 1 + 3 * (run t x).2 ∧ Pointer.Serves t (conditionalStep w t x).1 x k := by
  unfold conditionalStep
  split
  · exact run_pointer t x hx
  · have hsearch := locate_trace t x hx
    obtain ⟨ht, hk, _⟩ := locate_correct t x hx
    have hd : (locate t x).context.length = (run t x).2 := by
      unfold run
      cases he : (locate t x).focus with
      | nil => simp [Pointer.Config.key?, he] at hk
      | node l r => simp only [he]
    refine ⟨1 + (locate t x).context.length, by omega,
      ⟨locate t x, locate t x, (locate t x).context.length, 0,
        hsearch, hk, .refl, ht, by omega⟩⟩

end RotationBST.Splay
