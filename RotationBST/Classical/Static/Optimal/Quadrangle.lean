module

public import RotationBST.Classical.Static.Optimal.Recurrence
import Mathlib.Tactic

@[expose] public section

/-! Yao's speedup lemma (STOC 1980): if the interval weight satisfies the
quadrangle inequality and is monotone under inclusion, so does the optimal
cost, and the largest optimal roots are monotone (Knuth's inequalities). -/
namespace RotationBST.Classical.Static.Optimal

variable {W : Nat → Nat → Nat}

theorem cost_quadrangle_len (hQ : Quadrangle W) (hM : InclusionMonotone W) (len : Nat) :
    ∀ i i' j j', j' - i = len → i ≤ i' → i' ≤ j → j ≤ j' →
      cost W i j + cost W i' j' ≤ cost W i' j + cost W i j' := by
  induction len using Nat.strong_induction_on with
  | ind len ih =>
    intro i i' j j' hlen hii' hi'j hjj'
    by_cases hmid : i' = j
    · -- Empty middle: superadditivity `C(i, j) + C(j, j') ≤ C(i, j')`.
      subst hmid
      rw [cost_self, Nat.zero_add]
      by_cases hij : i = i'
      · subst hij; rw [cost_self]; omega
      by_cases hjj : i' = j'
      · subst hjj; rw [cost_self]; omega
      obtain ⟨hz1, hz2, hz3, _⟩ := root_spec W (show i < j' by omega)
      set z := root W i j'
      by_cases hz : z < i'
      · have h1 := cost_le_candidate W (i := i) (j := i') (r := z) hz1 hz
        have h2 := ih (j' - (z + 1)) (by omega) (z + 1) i' i' j' rfl (by omega) le_rfl hjj'
        have h3 := hM i i i' j' le_rfl (by omega) hjj'
        rw [cost_self, Nat.zero_add] at h2
        unfold candidate at h1 hz3
        omega
      · have h1 := cost_le_candidate W (i := i') (j := j') (r := z) (by omega) hz2
        have h2 := ih (z - i) (by omega) i i' i' z rfl hii' le_rfl (by omega)
        have h3 := hM i i' j' j' hii' hjj' le_rfl
        rw [cost_self, Nat.zero_add] at h2
        unfold candidate at h1 hz3
        omega
    · obtain ⟨hy1, hy2, hy3, _⟩ := root_spec W (show i' < j by omega)
      obtain ⟨hz1, hz2, hz3, _⟩ := root_spec W (show i < j' by omega)
      set y := root W i' j
      set z := root W i j'
      have hq := hQ i i' j j' hii' hi'j hjj'
      unfold candidate at hy3 hz3
      by_cases hzy : z ≤ y
      · have h1 := cost_le_candidate W (i := i) (j := j) (r := z) hz1 (by omega)
        have h2 := cost_le_candidate W (i := i') (j := j') (r := y) hy1 (by omega)
        have h3 := ih (j' - (z + 1)) (by omega) (z + 1) (y + 1) j j' rfl (by omega) (by omega) hjj'
        unfold candidate at h1 h2
        omega
      · have h1 := cost_le_candidate W (i := i) (j := j) (r := y) (by omega) hy2
        have h2 := cost_le_candidate W (i := i') (j := j') (r := z) (by omega) hz2
        have h3 := ih (z - i) (by omega) i i' y z rfl hii' hy1 (by omega)
        unfold candidate at h1 h2
        omega

/-- The optimal cost inherits the quadrangle inequality. -/
theorem cost_quadrangle (hQ : Quadrangle W) (hM : InclusionMonotone W) : Quadrangle (cost W) :=
  fun i i' j j' h1 h2 h3 => cost_quadrangle_len hQ hM (j' - i) i i' j j' rfl h1 h2 h3

/-- Knuth's first inequality: extending an interval to the right does not move
the largest optimal root to the left. -/
theorem root_le_root_right (hQ : Quadrangle W) (hM : InclusionMonotone W) {i j : Nat} (h : i < j) :
    root W i j ≤ root W i (j + 1) := by
  obtain ⟨hr1, hr2, hr3, _⟩ := root_spec W h
  obtain ⟨hs1, hs2, hs3, hsmax⟩ := root_spec W (show i < j + 1 by omega)
  set r := root W i j
  set s := root W i (j + 1)
  by_contra hlt
  have hq := cost_quadrangle hQ hM (s + 1) (r + 1) j (j + 1) (by omega) (by omega) (by omega)
  have hopt := cost_le_candidate W (i := i) (j := j) (r := s) hs1 (by omega)
  have hle : candidate W i (j + 1) r ≤ cost W i (j + 1) := by
    unfold candidate at hr3 hs3 hopt ⊢; omega
  have := hsmax r hr1 (by omega) (le_antisymm hle (cost_le_candidate W hr1 (by omega)))
  omega

/-- Knuth's second inequality: shrinking an interval from the left does not move
the largest optimal root to the left. -/
theorem root_le_root_left (hQ : Quadrangle W) (hM : InclusionMonotone W) {i j : Nat} (h : i + 1 < j) :
    root W i j ≤ root W (i + 1) j := by
  obtain ⟨hr1, hr2, hr3, _⟩ := root_spec W (show i < j by omega)
  obtain ⟨hs1, hs2, hs3, hsmax⟩ := root_spec W h
  set r := root W i j
  set s := root W (i + 1) j
  by_contra hlt
  have hq := cost_quadrangle hQ hM i (i + 1) s r (by omega) hs1 (by omega)
  have hopt := cost_le_candidate W (i := i) (j := j) (r := s) (by omega) hs2
  have hle : candidate W (i + 1) j r ≤ cost W (i + 1) j := by
    unfold candidate at hr3 hs3 hopt ⊢; omega
  have := hsmax r (by omega) hr2 (le_antisymm hle (cost_le_candidate W (by omega) hr2))
  omega

end RotationBST.Classical.Static.Optimal
