module

public import RotationBST.Splay.Updates.Execution.Abstract
public import RotationBST.Splay.Updates.Potential

@[expose] public section

namespace RotationBST.Splay.Updates

variable {s t : List Tree} {N m n c : Nat} {ns : List Nat}

noncomputable def forestPotential (ts : List Tree) : ℝ := (ts.map unitPotential).sum

theorem forestPotential_nonneg (ts : List Tree) : 0 ≤ forestPotential ts := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
      simp only [forestPotential, List.map_cons, List.sum_cons] at *
      linarith [unitPotential_nonneg t]

theorem forestSize_perm (h : s.Perm t) : forestSize s = forestSize t := (h.map Tree.size).sum_eq

theorem forestPotential_perm (h : s.Perm t) : forestPotential s = forestPotential t :=
  (h.map unitPotential).sum_eq

theorem forestPotential_upper (ts : List Tree) (N : Nat) (bound : forestSize ts ≤ N) :
    forestPotential ts ≤ (forestSize ts : ℝ) * Real.logb 2 (N + 1 : Nat) := by
  induction ts with
  | nil => simp [forestPotential, forestSize]
  | cons t ts ih =>
      have hs : t.size + forestSize ts ≤ N := bound
      have hi := ih (by omega)
      have ht := unitPotential_upper t
      have hm := mul_le_mul_of_nonneg_left
        (log_nat_mono (show t.size ≤ N + 1 by omega)) (Nat.cast_nonneg (α := ℝ) t.size)
      simp only [forestPotential, forestSize, List.map_cons, List.sum_cons, Nat.cast_add] at *
      nlinarith

/-- One uniform amortized bound for all five standard update operations. -/
theorem step_bound (h : Step s t c n) (N : Nat) (bound : forestSize s ≤ N) :
    (c : ℝ) + forestPotential t - forestPotential s ≤ 5 * Real.logb 2 (N + 1 : Nat) + 3 := by
  have hlog := Bounds.logb_nat_nonneg (N + 1)
  induction h with
  | @access x t hx =>
      have hb := unit_access t x hx
      have hs : t.size ≤ N := by simpa [forestSize] using bound
      have hm := log_nat_mono (show t.size ≤ N + 1 by omega)
      simp only [forestPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at hb hm hlog
      linarith
  | @insert k t hk =>
      have hb := insert_bound t k hk
      have hs : t.size ≤ N := by simpa [forestSize] using bound
      have hm := log_nat_mono (show t.size + 1 ≤ N + 1 by omega)
      simp only [forestPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at hb hm hlog
      linarith
  | @delete x t hx =>
      have hb := delete_bound t x hx
      have hs : t.size ≤ N := by simpa [forestSize] using bound
      have hm := log_nat_mono (show t.size ≤ N + 1 by omega)
      simp only [forestPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at hb hm hlog
      linarith
  | @split k t hk =>
      have hb := split_bound t k hk
      have hs : t.size ≤ N := by simpa [forestSize] using bound
      have hm := log_nat_mono (show t.size ≤ N + 1 by omega)
      simp only [forestPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at hb hm hlog
      linarith
  | @join l r =>
      have hb := join_bound l r
      have hs : l.size + r.size ≤ N := by simpa [forestSize] using bound
      have hm := log_nat_mono (show l.size + r.size ≤ N + 1 by omega)
      simp only [forestPotential, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, Nat.cast_add, Nat.cast_one]
      simp only [Nat.cast_add, Nat.cast_one] at hb hm hlog
      linarith
  | @frame s t c n a _ ih =>
      have hs : a.size + forestSize s ≤ N := bound
      have hi := ih (by omega)
      simp only [forestPotential, List.map_cons, List.sum_cons] at *
      linarith
  | rearrange hs _ ht ih =>
      have hi := ih (by rw [← forestSize_perm hs]; exact bound)
      rw [← forestPotential_perm hs, forestPotential_perm ht] at hi
      exact hi

theorem execution_amortized (h : Execution N s m t c) :
    (c : ℝ) + forestPotential t - forestPotential s ≤
      (m : ℝ) * (5 * Real.logb 2 (N + 1 : Nat) + 3) := by
  induction h with
  | nil => simp
  | cons bound hs _ ih =>
      have hb := step_bound hs N bound
      simp only [Nat.cast_add, Nat.cast_one] at hb ih ⊢
      nlinarith

/-- Balance theorem with updates, for a forest and arbitrary initial shapes.
`N` bounds all stored keys, `m` counts operations, and `c` includes request charges. -/
theorem balance (h : Execution N s m t c) :
    (c : ℝ) ≤ (m : ℝ) * (5 * Real.logb 2 (N + 1 : Nat) + 3) +
      (forestSize s : ℝ) * Real.logb 2 (forestSize s + 1 : Nat) := by
  have hb := execution_amortized h
  have hi := forestPotential_upper s (forestSize s) le_rfl
  have hf := forestPotential_nonneg t
  linarith

/-- The sharper bound charges only the tree(s) actually involved in a step. -/
theorem step_local_bound (h : Step s t c n) :
    (c : ℝ) + forestPotential t - forestPotential s ≤ 5 * Real.logb 2 (n + 1 : Nat) + 3 := by
  induction h with
  | access hx => exact step_bound (.access hx) _ (by simp [forestSize])
  | insert hk => exact step_bound (.insert hk) _ (by simp [forestSize])
  | delete hx => exact step_bound (.delete hx) _ (by simp [forestSize])
  | split hk => exact step_bound (.split hk) _ (by simp [forestSize])
  | join => exact step_bound .join _ (by simp [forestSize])
  | frame _ ih =>
      simp only [forestPotential, List.map_cons, List.sum_cons] at *
      linarith
  | rearrange hs _ ht ih =>
      rw [← forestPotential_perm hs, forestPotential_perm ht] at ih
      exact ih

theorem local_execution_amortized (h : LocalExecution s ns t c) :
    (c : ℝ) + forestPotential t - forestPotential s ≤
      (ns.map fun n : Nat => 5 * Real.logb 2 (n + 1 : Nat) + 3).sum := by
  induction h with
  | nil => simp
  | cons hs _ ih =>
      have hb := step_local_bound hs
      simp only [Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons] at hb ih ⊢
      linarith

/-- The operation-sensitive balance theorem: different requests may involve
very different tree sizes, and unrelated trees contribute no logarithmic charge. -/
theorem balance_local (h : LocalExecution s ns t c) :
    (c : ℝ) ≤ (ns.map fun n : Nat => 5 * Real.logb 2 (n + 1 : Nat) + 3).sum +
      (forestSize s : ℝ) * Real.logb 2 (forestSize s + 1 : Nat) := by
  have hb := local_execution_amortized h
  have hi := forestPotential_upper s (forestSize s) le_rfl
  have hf := forestPotential_nonneg t
  linarith

/-- The paper's initially-empty version has no initialization allowance. -/
theorem balance_initially_empty (h : LocalExecution s ns t c) (empty : forestSize s = 0) :
    (c : ℝ) ≤ (ns.map fun n : Nat => 5 * Real.logb 2 (n + 1 : Nat) + 3).sum := by
  have hb := balance_local h
  simpa [empty] using hb

end RotationBST.Splay.Updates
