module

public import RotationBST.Classical.Scapegoat.Analysis
import Mathlib.Tactic

@[expose] public section

/-! The height and cost bounds of scapegoat trees, in real logarithms. -/
namespace RotationBST.Classical.Scapegoat
open Dictionary

variable {α : ℚ}

theorem one_lt_inv_alpha (hα : 1 / 2 < α ∧ α < 1) : (1 : ℝ) < 1 / (α : ℝ) := by
  have : (0 : ℝ) < α := by exact_mod_cast (show (0 : ℚ) < α by linarith)
  rw [lt_div_iff₀ this, one_mul]; exact_mod_cast hα.2

/-- Every depth is at most `log_{1/α} n + 1`. -/
theorem depth_bound (hα : 1 / 2 < α ∧ α < 1) (s : State) (h : Inv α s) (z : Nat) (hz : z < s.1.size) :
    (s.1.depth z : ℝ) ≤ Real.logb (1 / α) s.1.size + 1 := by
  obtain ⟨_, hN, hd⟩ := h
  have ha : (0 : ℝ) < α := by exact_mod_cast (show (0 : ℚ) < α by linarith)
  have hd' : (1 : ℝ) ≤ (α : ℝ) ^ s.1.depth z * s.2 := by exact_mod_cast hd z hz
  have hN' : (α : ℝ) * s.2 ≤ s.1.size := by exact_mod_cast hN
  have hn : (0 : ℝ) < s.1.size := by exact_mod_cast (show 0 < s.1.size by omega)
  -- `(1/α)^d ≤ N ≤ n / α`.
  have hpow : (1 / (α : ℝ)) ^ s.1.depth z ≤ s.1.size * (1 / α) := by
    have hp : 0 < (α : ℝ) ^ s.1.depth z := pow_pos ha _
    rw [div_pow, one_pow]
    rw [div_le_iff₀ hp]
    calc (1 : ℝ) ≤ α ^ s.1.depth z * s.2 := hd'
      _ ≤ α ^ s.1.depth z * (s.1.size * (1 / α)) := by
          apply mul_le_mul_of_nonneg_left _ hp.le
          rw [mul_one_div, le_div_iff₀ ha]; linarith
      _ = s.1.size * (1 / α) * α ^ s.1.depth z := by ring
  have hb := one_lt_inv_alpha hα
  have := (Real.le_logb_iff_rpow_le (x := (s.1.depth z : ℝ)) (y := (s.1.size : ℝ) * (1 / α)) hb
    (by positivity)).mpr (by rw [Real.rpow_natCast]; exact hpow)
  rw [Real.logb_mul hn.ne' (by positivity), Real.logb_self_eq_one hb] at this
  exact this

theorem bound_mono (hα : 1 / 2 < α ∧ α < 1) {n m : Nat} (h : n ≤ m) : bound α n ≤ bound α m := by
  unfold bound
  have hK : (0 : ℝ) ≤ 2 / (2 * (α : ℝ) - 1) + 1 := by
    have : (1 : ℝ) < 2 * α := by exact_mod_cast (show (1 : ℚ) < 2 * α by linarith)
    have : (0 : ℝ) < 2 / (2 * (α : ℝ) - 1) := by apply div_pos <;> linarith
    linarith
  have hl : Real.logb (1 / α) n ≤ Real.logb (1 / α) m := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [Nat.cast_zero, Real.logb_zero]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · exact Real.logb_nonneg (one_lt_inv_alpha hα) (by exact_mod_cast hm)
    · exact Real.logb_le_logb_of_le (one_lt_inv_alpha hα) (by exact_mod_cast h0) (by exact_mod_cast h)
  nlinarith

/-- Amortized cost of one step, with logarithms. -/
theorem step_bound (hα : 1 / 2 < α ∧ α < 1) (s : State) (op : Op) (valid : op.Valid s.1.size)
    (h : Inv α s) :
    ((step α s op).2 : ℝ) + (potential α (step α s op).1 : ℝ) ≤ potential α s + bound α s.1.size := by
  set D := Real.logb (1 / α) s.1.size + 1
  have hD : 0 ≤ D := by
    rcases Nat.eq_zero_or_pos s.1.size with h0 | h0
    · simp [D, h0]
    · have := Real.logb_nonneg (one_lt_inv_alpha hα) (show (1 : ℝ) ≤ s.1.size by exact_mod_cast h0)
      simp only [D]; linarith
  set e := ⌊D⌋₊
  have he : ∀ z < s.1.size, s.1.depth z ≤ e := fun z hz => Nat.le_floor (depth_bound hα s h z hz)
  have hq := step_amortized hα s op valid h e he
  have hr := (Rat.cast_le (K := ℝ)).2 hq
  have heD : (e : ℝ) ≤ D := Nat.floor_le hD
  have hK : (0 : ℝ) ≤ 2 / (2 * (α : ℝ) - 1) + 1 := by
    have : (1 : ℝ) < 2 * α := by exact_mod_cast (show (1 : ℚ) < 2 * α by linarith)
    have : (0 : ℝ) < 2 / (2 * (α : ℝ) - 1) := by apply div_pos <;> linarith
    linarith
  push_cast at hr
  unfold bound
  simp only [D] at heD
  nlinarith

theorem run_bound (hα : 1 / 2 < α ∧ α < 1) (s : State) (ops : List Op)
    (valid : Op.ValidSeq s.1.size ops) (h : Inv α s) :
    ((run α s ops).2 : ℝ) + (potential α (run α s ops).1 : ℝ) ≤
      potential α s + ((sizesFrom s.1.size ops).map (bound α)).sum := by
  induction ops generalizing s with
  | nil => simp [run, sizesFrom]
  | cons op ops ih =>
    have h1 := step_bound hα s op valid.1 h
    have h2 := ih (step α s op).1 (by rw [step_size s op valid.1]; exact valid.2) (step_inv hα s op valid.1 h)
    rw [step_size s op valid.1] at h2
    simp only [run, sizesFrom, List.map_cons, List.sum_cons]
    push_cast
    linarith

theorem sizesFrom_length (n : Nat) (ops : List Op) : (sizesFrom n ops).length = ops.length := by
  induction ops generalizing n with
  | nil => rfl
  | cons op ops ih => simp [sizesFrom, ih]

theorem sizesFrom_le (n : Nat) (ops : List Op) : ∀ x ∈ sizesFrom n ops, x ≤ n + ops.length := by
  induction ops generalizing n with
  | nil => simp [sizesFrom]
  | cons op ops ih =>
    intro x hx
    simp only [sizesFrom, List.mem_cons] at hx
    have hr : op.resize n ≤ n + 1 := by cases op <;> simp only [Op.resize] <;> omega
    rcases hx with rfl | hx
    · simp
    · have := ih _ x hx; simp only [List.length_cons]; omega

/-- **Total cost from the empty tree**: at most the sum of the amortized bounds. -/
theorem total_cost (hα : 1 / 2 < α ∧ α < 1) (ops : List Op) (valid : Op.ValidSeq 0 ops) :
    ((run α (.nil, 0) ops).2 : ℝ) ≤ ((sizesFrom 0 ops).map (bound α)).sum := by
  have v : Op.ValidSeq (Tree.nil, 0).1.size ops := by simpa [Tree.size] using valid
  have := run_bound hα (.nil, 0) ops v inv_empty
  have hp := potential_nonneg hα _ (run_inv hα (.nil, 0) ops v inv_empty)
  have h0 : potential α (.nil, 0) = 0 := by simp [potential, phi, Tree.size]
  rw [h0] at this
  have hp' : (0 : ℝ) ≤ (potential α (run α (.nil, 0) ops).1 : ℝ) := by exact_mod_cast hp
  simp only [Tree.size, Rat.cast_zero, zero_add] at this
  linarith

theorem total_cost_le (hα : 1 / 2 < α ∧ α < 1) (ops : List Op) (valid : Op.ValidSeq 0 ops) :
    ((run α (.nil, 0) ops).2 : ℝ) ≤ ops.length * bound α ops.length := by
  have h := total_cost hα ops valid
  have hle : ((sizesFrom 0 ops).map (bound α)).sum ≤ ((sizesFrom 0 ops).map fun _ => bound α ops.length).sum :=
    List.sum_le_sum fun x hx => bound_mono hα (by simpa using sizesFrom_le 0 ops x hx)
  rw [List.map_const', List.sum_replicate, sizesFrom_length, nsmul_eq_mul] at hle
  linarith

/-- From the empty tree, every reachable tree has depths at most `log_{1/α} n + 1`. -/
theorem reachable_depth (hα : 1 / 2 < α ∧ α < 1) (ops : List Op) (valid : Op.ValidSeq 0 ops)
    (z : Nat) (hz : z < (run α (.nil, 0) ops).1.1.size) :
    ((run α (.nil, 0) ops).1.1.depth z : ℝ) ≤ Real.logb (1 / α) (run α (.nil, 0) ops).1.1.size + 1 :=
  depth_bound hα _ (run_inv hα (.nil, 0) ops (by simpa [Tree.size] using valid) inv_empty) z hz

end RotationBST.Classical.Scapegoat
