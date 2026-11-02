module

public import RotationBST.WorkingSet.LogBound
public import RotationBST.WorkingSet.Distinct
public import RotationBST.Splay.WeightedBound

@[expose] public section

namespace RotationBST.Splay
open Recency

/-- The changing recency weights telescope because reweighting after splaying
cannot increase potential. The history is chronological throughout. -/
theorem workingSet_amortized (past : List Nat) (t : Tree) (xs : List Nat)
    (pastValid : ∀ x ∈ past, x < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    ((algorithm.runFrom past t xs).2 : ℝ) +
      potential (weight (recent t.size (past ++ xs))) (algorithm.runFrom past t xs).1 0 -
      potential (weight (recent t.size past)) t 0 ≤
        10 * (workingSetSum t.size past xs : ℝ) := by
  induction xs generalizing past t with
  | nil => simp [Algorithm.runFrom, workingSetSum]
  | cons x xs ih =>
      have hx := valid x (by simp)
      have ha := (run_correct t x hx).1
      have hb := access_bound (recent t.size past) t x (recent_perm t.size past pastValid) hx
      have hr := rank_le_workingSet t.size x past pastValid hx
      have hl : ((recent t.size past).idxOf x + 1).log2 ≤ (workingSetNumber t.size past x).log2 := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right hr
      have hl' : (((recent t.size past).idxOf x + 1).log2 : ℝ) ≤
          (workingSetNumber t.size past x).log2 := by exact_mod_cast hl
      rcases he : run t x with ⟨u, k⟩
      rw [he] at ha hb
      have hs := ha.1.size_eq
      have hv : ∀ y ∈ xs, y < u.size := by
        intro y hy; rw [← hs]; exact valid y (by simp [hy])
      have hp : ∀ y ∈ past ++ [x], y < u.size := by
        intro y hy
        rw [← hs]
        rcases List.mem_append.mp hy with hy | hy
        · exact pastValid y hy
        · simpa using (List.mem_singleton.mp hy ▸ hx)
      have hi := ih (past ++ [x]) u hp hv
      rw [← hs] at hi
      simp only [List.append_assoc, List.singleton_append, recent_step] at hi
      rcases hf : algorithm.runFrom (past ++ [x]) u xs with ⟨v, m⟩
      rw [hf] at hi
      have he' : algorithm.step past t x = (u, k) := he
      simp only [Algorithm.runFrom, he', hf, workingSetSum, Nat.cast_add, Nat.cast_one]
      dsimp only at hb hi ⊢
      linarith

/-- All recency potentials lie in an interval of width `O(n log n)`, uniformly
in the order of the keys and the shape of the tree. -/
theorem recency_potential_bounds (order : List Nat) (t : Tree)
    (hp : order.Perm (List.range t.size)) :
    -2 * (t.size : ℝ) * Real.logb 2 ((t.size : ℝ) + 1) ≤ potential (weight order) t 0 ∧
      potential (weight order) t 0 ≤ t.size := by
  have hlen : order.length = t.size := hp.length_eq.trans List.length_range
  have hlow : ∀ i, (((t.size : ℝ) + 1) ^ 2)⁻¹ ≤ weight order i := by
    intro i; simpa only [hlen] using weight_lower order i
  have hmass : mass (weight order) t 0 ≤ 2 := by
    rw [mass_weight order t hp]; exact squareSum_le_two _
  obtain ⟨hl, hu⟩ := potential_bounds (weight order) (weight_pos order)
    ((((t.size : ℝ) + 1) ^ 2)⁻¹) 2 (by positivity) hlow t 0 hmass
  rw [Real.logb_inv, Real.logb_pow] at hl
  rw [Real.logb_self_eq_one (by norm_num), mul_one] at hu
  norm_num only [Nat.cast_ofNat] at hl
  constructor
  · nlinarith
  · exact hu

theorem initial_allowance (n : Nat) :
    (n : ℝ) * (1 + 2 * Real.logb 2 ((n : ℝ) + 1)) ≤
      6 * (n : ℝ) * (1 + (n.log2 : ℝ)) := by
  by_cases hn : n = 0
  · subst n; simp
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < (n : ℝ) + 1) (show (n : ℝ) + 1 ≤ 2 * n by linarith)
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)] at hl
    have hnlog := logb_nat_le n
    have hlog : Real.logb 2 ((n : ℝ) + 1) ≤ (n.log2 : ℝ) + 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) n)
    have hnn : 0 ≤ (n : ℝ) * n.log2 := by positivity
    nlinarith

/-- Splaying satisfies the working-set bound in the original integer-log model.
The constants include arbitrary initial shape and first access charged at `n`. -/
theorem workingSet_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    algorithm.cost t xs ≤ 10 * workingSetSum t.size [] xs +
      6 * t.size * (1 + t.size.log2) := by
  have hb := workingSet_amortized [] t xs (by simp) valid
  simp only [List.nil_append] at hb
  have he := algorithm.execution [] t xs valid
  have hs := he.size_eq
  have hp := recent_perm t.size xs valid
  have hp' : (recent t.size xs).Perm (List.range (algorithm.runFrom [] t xs).1.size) := by
    rw [← hs]; exact hp
  have hf := (recency_potential_bounds _ _ hp').1
  rw [← hs] at hf
  have hi := (recency_potential_bounds (recent t.size []) t (recent_perm t.size [] (by simp))).2
  have hallow := initial_allowance t.size
  have h : (algorithm.cost t xs : ℝ) ≤ 10 * (workingSetSum t.size [] xs : ℝ) +
      6 * (t.size : ℝ) * (1 + (t.size.log2 : ℝ)) := by
    unfold Algorithm.cost
    nlinarith
  exact_mod_cast h

/-- The splay algorithm has the working-set property, with uniform constants. -/
theorem hasWorkingSetBound : HasWorkingSetBound algorithm :=
  ⟨10, 6, workingSet_bound⟩

end RotationBST.Splay
