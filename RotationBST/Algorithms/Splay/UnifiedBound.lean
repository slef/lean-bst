module

public import RotationBST.Algorithms.Splay.Unified

@[expose] public section

namespace RotationBST.Splay
open Recency

/-- Telescope the changing mixed-weight potential along the actual splay run. -/
theorem unified_amortized (original past : List Nat) (f : Nat) (t : Tree) (xs : List Nat)
    (originalValid : ∀ x ∈ original, x < t.size)
    (pastValid : ∀ x ∈ past, x < t.size) (sub : ∀ x ∈ xs, x ∈ original) :
    ((algorithm.runFrom past t xs).2 : ℝ) +
      potential (mixedWeight (unifiedFixed original f) (recent t.size (past ++ xs)))
        (algorithm.runFrom past t xs).1 0 -
      potential (mixedWeight (unifiedFixed original f) (recent t.size past)) t 0 ≤
        10 * unifiedSum t.size f original past xs := by
  induction xs generalizing past t with
  | nil => simp [Algorithm.runFrom, unifiedSum]
  | cons x xs ih =>
      have hx := sub x (by simp)
      have hvalid := originalValid x hx
      have ha := (run_correct t x hvalid).1
      have hb := unified_access original past f t x originalValid pastValid hx
      rcases he : run t x with ⟨u, k⟩
      rw [he] at ha hb
      have hs := ha.1.size_eq
      have hv : ∀ y ∈ original, y < u.size := by
        intro y hy; rw [← hs]; exact originalValid y hy
      have hp : ∀ y ∈ past ++ [x], y < u.size := by
        intro y hy
        rw [← hs]
        rcases List.mem_append.mp hy with hy | hy
        · exact pastValid y hy
        · simpa using (List.mem_singleton.mp hy ▸ hvalid)
      have hi := ih (past ++ [x]) u hv hp (by intro y hy; exact sub y (by simp [hy]))
      rw [← hs] at hi
      simp only [List.append_assoc, List.singleton_append] at hi
      rcases hf : algorithm.runFrom (past ++ [x]) u xs with ⟨v, m⟩
      rw [hf] at hi
      have he' : algorithm.step past t x = (u, k) := he
      simp only [Algorithm.runFrom, he', hf, unifiedSum, Nat.cast_add]
      dsimp only at hb hi ⊢
      linarith

theorem mixed_potential_bounds (fixed : Nat → ℝ) (hf : ∀ i, 0 ≤ fixed i)
    (order : List Nat) (t : Tree) (hp : order.Perm (List.range t.size))
    (hfixed : mass fixed t 0 ≤ 5) :
    -2 * (t.size : ℝ) * Real.logb 2 ((t.size : ℝ) + 1) ≤
      potential (mixedWeight fixed order) t 0 ∧
      potential (mixedWeight fixed order) t 0 ≤ 3 * t.size := by
  have hlen : order.length = t.size := hp.length_eq.trans List.length_range
  have hlow : ∀ i, (((t.size : ℝ) + 1) ^ 2)⁻¹ ≤ mixedWeight fixed order i := by
    intro i
    have h := weight_lower order i
    rw [hlen] at h
    exact h.trans (le_add_of_nonneg_right (hf i))
  have hmass : mass (mixedWeight fixed order) t 0 ≤ 8 := by
    change mass (fun i => weight order i + fixed i) t 0 ≤ 8
    rw [mass_add, mass_weight order t hp]
    linarith [squareSum_le_two t.size]
  obtain ⟨hl, hu⟩ := potential_bounds _ (mixedWeight_pos fixed hf order)
    ((((t.size : ℝ) + 1) ^ 2)⁻¹) 8 (by positivity) hlow t 0 hmass
  rw [Real.logb_inv, Real.logb_pow] at hl
  have h8 : Real.logb 2 8 = 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [h8] at hu
  norm_num only [Nat.cast_ofNat] at hl
  constructor <;> nlinarith

theorem unifiedCharge_ge_one (n f : Nat) (original past : List Nat) (x : Nat)
    (hx : x ∈ original) : 1 ≤ unifiedCharge n f original past x := by
  have hq : (0 : ℝ) < original.count x := by exact_mod_cast List.count_pos_iff.mpr hx
  have hqm : (original.count x : ℝ) ≤ original.length := by exact_mod_cast List.count_le_length
  have hf := Real.logb_nonneg (b := (2 : ℝ)) (by norm_num)
    ((le_div_iff₀ hq).mpr (show (1 : ℝ) * original.count x ≤ original.length by simpa using hqm))
  have hw := Bounds.logb_nat_nonneg (workingSetNumber n past x)
  have hd := Bounds.logb_nat_nonneg (Nat.dist x f + 1)
  unfold unifiedCharge
  have := le_min hw (le_min hf hd)
  linarith

theorem length_le_unifiedSum (n f : Nat) (original past xs : List Nat)
    (sub : ∀ x ∈ xs, x ∈ original) : (xs.length : ℝ) ≤ unifiedSum n f original past xs := by
  induction xs generalizing past with
  | nil => simp [unifiedSum]
  | cons x xs ih =>
      have hx := unifiedCharge_ge_one n f original past x (sub x (by simp))
      have hi := ih (past ++ [x]) (by intro y hy; exact sub y (by simp [hy]))
      simp only [unifiedSum, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- Sleator--Tarjan's unified theorem: the choice among the three bounds is made
separately at each request. This includes an arbitrary initial-tree allowance. -/
theorem unified_bound (t : Tree) (xs : List Nat) (f : Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    (algorithm.totalCost t xs : ℝ) ≤ 11 * unifiedSum t.size f xs [] xs +
      8 * (t.size : ℝ) * (1 + (t.size.log2 : ℝ)) := by
  have hb := unified_amortized xs [] f t xs valid (by simp) (by intro x hx; exact hx)
  simp only [List.nil_append] at hb
  have he := algorithm.execution [] t xs valid
  have hs := he.size_eq
  have hp := recent_perm t.size xs valid
  have hp' : (recent t.size xs).Perm (List.range (algorithm.runFrom [] t xs).1.size) := by
    rw [← hs]; exact hp
  have hfixed := unifiedFixed_mass xs f t valid
  have hfixed' : mass (unifiedFixed xs f) (algorithm.runFrom [] t xs).1 0 ≤ 5 := by
    rw [← execution_mass_eq _ he]; exact hfixed
  have hf := (mixed_potential_bounds _ (unifiedFixed_nonneg xs f) _ _ hp' hfixed').1
  rw [← hs] at hf
  have hi := (mixed_potential_bounds _ (unifiedFixed_nonneg xs f) (recent t.size []) t
    (recent_perm t.size [] (by simp)) hfixed).2
  have hallow := initial_allowance t.size
  have hlen := length_le_unifiedSum t.size f xs [] xs (by intro x hx; exact hx)
  simp only [Algorithm.totalCost, Algorithm.cost, Nat.cast_add]
  nlinarith [Nat.cast_nonneg (α := ℝ) t.size, Nat.cast_nonneg (α := ℝ) t.size.log2]

end RotationBST.Splay
