module

public import RotationBST.Classical.Scapegoat.Fix
import Mathlib.Tactic

@[expose] public section

/-! Scapegoat trees: every step is a dictionary step; the height invariant
`α^depth · N ≥ 1` with `α N ≤ n ≤ N` is maintained; and the potential
`K Φ + L (N - n)` with `K = 2/(2α - 1)`, `L = 2α/(1 - α)` pays for rebuilding. -/
namespace RotationBST.Classical.Scapegoat
open _root_.RotationBST.Tree (balanced)
open WeightBalanced Static Dictionary

variable {α : ℚ}

/-! ### Dictionary steps -/

theorem step_dictionary (s : State) (op : Op) (valid : op.Valid s.1.size) :
    Dictionary.Step s.1.unit op (step α s op).1.1.unit (step α s op).2 0 := by
  cases op with
  | access x =>
    have := Step.access (s := s.1.unit) (x := x) (by simpa [Op.Valid] using valid) .refl
    simpa [step] using this
  | insert k =>
    have sp := unit_insertAt_splice s.1 k (by simpa [Op.Valid] using valid)
    have v : k ≤ s.1.unit.erase.size := by simpa [Op.Valid] using valid
    simp only [step]
    split
    · cases hf : fix α (Tree.insertAt s.1 k) k with
      | some p =>
        have m := moves_of_rotations (rotations_unit (fix_spec _ k p hf).1)
        have := Step.insert v .refl sp m
        simpa using this
      | none =>
        have := Step.insert v .refl sp .refl
        simpa using this
    · have := Step.insert v .refl sp .refl
      simpa using this
  | delete x =>
    obtain ⟨sp, tg⟩ := bstDelete_splice s.1 x (by simpa [Op.Valid] using valid)
    have v : x < s.1.unit.erase.size := by simpa [Op.Valid] using valid
    have tg' : deleteTarget s.1 x = x ∨
        (s.1.unit.erase.TwoChildren x ∧ (deleteTarget s.1 x + 1 = x ∨ deleteTarget s.1 x = x + 1)) := by
      rcases tg with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simpa using h1, Or.inr h2⟩
    simp only [step]
    split
    · have m := moves_of_rotations (rotations_unit (rebuild_rotations (bstDelete s.1 x)))
      have := Step.delete v tg' .refl sp m
      simpa using this
    · have := Step.delete v tg' .refl sp .refl
      simpa using this

theorem step_size (s : State) (op : Op) (valid : op.Valid s.1.size) :
    (step α s op).1.1.size = op.resize s.1.size := by
  have := (step_dictionary (α := α) s op valid).size
  simpa using this

theorem run_execution (s : State) (ops : List Op) (valid : Op.ValidSeq s.1.size ops) :
    Dictionary.Execution s.1.unit ops (run α s ops).1.1.unit (run α s ops).2 0 := by
  induction ops generalizing s with
  | nil => exact .nil
  | cons op ops ih =>
    have st := step_dictionary (α := α) s op valid.1
    have rest := ih (step α s op).1 (by rw [step_size s op valid.1]; exact valid.2)
    simpa [run] using Dictionary.Execution.cons st rest

/-! ### The invariant -/

/-- `n ≤ N`, `α N ≤ n`, and every key at depth `e` has `α^e N ≥ 1`. -/
def Inv (α : ℚ) (s : State) : Prop :=
  s.1.size ≤ s.2 ∧ α * s.2 ≤ s.1.size ∧ ∀ z < s.1.size, 1 ≤ α ^ s.1.depth z * s.2

theorem inv_empty : Inv α (.nil, 0) := by simp [Inv, Tree.size]

/-- The balanced tree on `n` keys meets the depth condition with `N = n`. -/
theorem balanced_inv (hα : 1 / 2 ≤ α) (n z : Nat) (hz : z < n) :
    1 ≤ α ^ (balanced n).depth z * n := by
  have hd := balanced_depth n z hz
  have h2 : 2 ^ (balanced n).depth z ≤ n :=
    (Nat.pow_le_pow_right (by norm_num) hd).trans (Nat.log2_self_le (by omega))
  have hp : (1 / 2 : ℚ) ^ (balanced n).depth z ≤ α ^ (balanced n).depth z :=
    pow_le_pow_left₀ (by norm_num) hα _
  have h2' : ((2 ^ (balanced n).depth z : Nat) : ℚ) ≤ n := by exact_mod_cast h2
  push_cast at h2'
  calc (1 : ℚ) = (1 / 2) ^ (balanced n).depth z * 2 ^ (balanced n).depth z := by
        rw [← mul_pow]; norm_num
    _ ≤ α ^ (balanced n).depth z * n := by
        apply mul_le_mul hp h2' (by positivity) (by positivity)

theorem step_inv (hα : 1 / 2 < α ∧ α < 1) (s : State) (op : Op) (valid : op.Valid s.1.size)
    (h : Inv α s) : Inv α (step α s op).1 := by
  obtain ⟨hn, hN, hd⟩ := h
  have hα0 : 0 ≤ α ∧ α ≤ 1 := ⟨by linarith, by linarith⟩
  cases op with
  | access x => exact ⟨hn, hN, hd⟩
  | insert k =>
    simp only [Op.Valid] at valid
    simp only [step]
    set t₁ := Tree.insertAt s.1 k with ht₁
    set N := max s.2 (s.1.size + 1) with hNdef
    have hs₁ : t₁.size = s.1.size + 1 := insertAt_size _ _
    have hNN : (s.2 : ℚ) ≤ N := by exact_mod_cast le_max_left _ _
    have hnN : s.1.size + 1 ≤ N := le_max_right _ _
    have hαN : α * N ≤ s.1.size + 1 := by
      rcases le_total s.2 (s.1.size + 1) with hle | hle
      · rw [show N = s.1.size + 1 from max_eq_right hle]; push_cast; nlinarith
      · rw [show N = s.2 from max_eq_left hle]; linarith
    -- Old keys meet the condition for the larger `N`.
    have hold : ∀ z < t₁.size, z ≠ k → 1 ≤ α ^ t₁.depth z * N := by
      intro z hz hzk
      obtain ⟨x, hx, he⟩ := insertAt_depth_other s.1 k z valid (by omega) hzk
      rw [he]
      exact (hd x hx).trans (mul_le_mul_of_nonneg_left hNN (pow_nonneg hα0.1 _))
    have base : t₁.size ≤ N ∧ α * N ≤ t₁.size := ⟨by omega, by rw [hs₁]; push_cast; exact hαN⟩
    split
    · rename_i hdeep
      -- The tree was not empty, so the new leaf has a parent.
      have hne : s.1 ≠ .nil := by
        intro he
        have hk0 : k = 0 := by simp [he, Tree.size] at valid; omega
        have : t₁.depth k = 0 := by simp [t₁, he, hk0, Tree.insertAt, Tree.depth, Tree.size]
        rw [this, pow_zero, one_mul] at hdeep
        have : (1 : ℚ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        linarith
      obtain ⟨x, hx, hpar⟩ := insertAt_parent s.1 k valid hne
      cases hf : fix α t₁ k with
      | some p =>
        have hsp := (fix_spec _ k p hf).2
        refine ⟨by rw [hsp]; exact base.1, by rw [hsp]; exact base.2, ?_⟩
        have := fix_depth hα.1.le (fun e => 1 ≤ α ^ e * N)
          (fun a b hab hb => hb.trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hα0.1 hα0.2 hab) (by positivity)))
          t₁ k 0 p (by omega) hf (by simpa using hold)
          (by
            simp only [Nat.zero_add]
            rw [hpar, Nat.add_sub_cancel]
            exact (hd x hx).trans (mul_le_mul_of_nonneg_left hNN (pow_nonneg hα0.1 _)))
        simpa using this
      | none =>
        exfalso
        have hn := fix_none t₁ k (by omega) hf
        unfold Violates at hn
        rw [not_lt, hs₁] at hn
        have : α ^ t₁.depth k * ((s.1.size + 1 : Nat) : ℚ) ≤ α ^ t₁.depth k * N :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (pow_nonneg hα0.1 _)
        push_cast at hn this
        linarith
    · rename_i hdeep
      refine ⟨base.1, base.2, fun z hz => ?_⟩
      by_cases hzk : z = k
      · subst hzk; exact not_lt.mp hdeep
      · exact hold z hz hzk
  | delete x =>
    simp only [Op.Valid] at valid
    have hs₁ := bstDelete_size s.1 x valid
    simp only [step]
    split
    · rename_i hsmall
      unfold Inv; dsimp only
      refine ⟨by rw [rebuild_size], by rw [rebuild_size]; nlinarith [(Nat.cast_nonneg (α := ℚ) (bstDelete s.1 x).size)], ?_⟩
      intro z hz
      rw [rebuild_size] at hz
      exact balanced_inv hα.1.le _ z hz
    · rename_i hbig
      unfold Inv; dsimp only
      refine ⟨by omega, not_lt.mp hbig, fun z hz => ?_⟩
      have sp := (bstDelete_splice s.1 x valid).1
      obtain ⟨z₀, h₀, hdz⟩ := splice_depth sp z (by simpa using hz)
      simp only [unit_erase] at h₀ hdz
      exact (hd z₀ h₀).trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hα0.1 hα0.2 hdz) (by positivity))

theorem run_inv (hα : 1 / 2 < α ∧ α < 1) (s : State) (ops : List Op)
    (valid : Op.ValidSeq s.1.size ops) (h : Inv α s) : Inv α (run α s ops).1 := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih =>
    exact ih _ (by rw [step_size s op valid.1]; exact valid.2) (step_inv hα s op valid.1 h)

/-! ### Amortization -/

/-- The potential `K Φ + L (N - n)`. -/
def potential (α : ℚ) (s : State) : ℚ :=
  2 / (2 * α - 1) * phi s.1 + 2 * α / (1 - α) * ((s.2 : ℚ) - s.1.size)

theorem potential_nonneg (hα : 1 / 2 < α ∧ α < 1) (s : State) (h : Inv α s) : 0 ≤ potential α s := by
  have hK : 0 < 2 / (2 * α - 1) := by apply div_pos <;> linarith
  have hL : 0 < 2 * α / (1 - α) := by apply div_pos <;> linarith
  have : (s.1.size : ℚ) ≤ s.2 := by exact_mod_cast h.1
  unfold potential
  have : (0 : ℚ) ≤ phi s.1 := by positivity
  nlinarith

/-- Amortized cost of one step, with `e` any bound on the heights. -/
theorem step_amortized (hα : 1 / 2 < α ∧ α < 1) (s : State) (op : Op) (valid : op.Valid s.1.size)
    (h : Inv α s) (e : Nat) (he : ∀ z < s.1.size, s.1.depth z ≤ e) :
    ((step α s op).2 : ℚ) + potential α (step α s op).1 ≤
      potential α s + (2 / (2 * α - 1) + 1) * (e + 1) + 1 + 2 * α / (1 - α) := by
  obtain ⟨hn, hN, hd⟩ := h
  set K := 2 / (2 * α - 1) with hKdef
  set L := 2 * α / (1 - α) with hLdef
  have hK : 0 < K := by apply div_pos <;> linarith
  have hL : 0 < L := by apply div_pos <;> linarith
  have hφ : (0 : ℚ) ≤ phi s.1 := by positivity
  have hnN : (s.1.size : ℚ) ≤ s.2 := by exact_mod_cast hn
  have he' : (0 : ℚ) ≤ e := by positivity
  cases op with
  | access x =>
    simp only [Op.Valid] at valid
    have := he x valid
    simp only [step]
    have : ((s.1.depth x + 1 : Nat) : ℚ) ≤ e + 1 := by exact_mod_cast (by omega : s.1.depth x + 1 ≤ e + 1)
    nlinarith
  | insert k =>
    simp only [Op.Valid] at valid
    simp only [step]
    set t₁ := Tree.insertAt s.1 k with ht₁
    set N := max s.2 (s.1.size + 1) with hNdef
    have hs₁ : t₁.size = s.1.size + 1 := insertAt_size _ _
    -- The new leaf is at depth at most `e + 1`.
    have hdk : t₁.depth k ≤ e + 1 := by
      by_cases hne : s.1 = .nil
      · have hk0 : k = 0 := by simp [hne, Tree.size] at valid; omega
        have : t₁.depth k = 0 := by simp [t₁, hne, hk0, Tree.insertAt, Tree.depth, Tree.size]
        omega
      · obtain ⟨x, hx, hpar⟩ := insertAt_parent s.1 k valid hne
        rw [← ht₁] at hpar
        have := he x hx; omega
    have hdk' : (t₁.depth k : ℚ) ≤ e + 1 := by exact_mod_cast hdk
    have hφ₁ : (phi t₁ : ℚ) ≤ phi s.1 + t₁.depth k := by exact_mod_cast phi_insertAt s.1 k
    have hΨ : (N : ℚ) - (s.1.size + 1 : Nat) ≤ s.2 - s.1.size := by
      rcases le_total s.2 (s.1.size + 1) with hle | hle
      · rw [show N = s.1.size + 1 from max_eq_right hle]; push_cast; linarith
      · rw [show N = s.2 from max_eq_left hle]; push_cast; linarith
    split
    · cases hf : fix α t₁ k with
      | some p =>
        have hsp := (fix_spec _ k p hf).2
        obtain ⟨hpay, _⟩ := fix_phi hα.1 t₁ k p (by omega) hf
        have hpay' : (p.2 : ℚ) ≤ K * (phi t₁ - phi p.1) := by
          rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith
        simp only [potential, hsp, hs₁] at hΨ ⊢
        push_cast at hΨ hpay' ⊢
        nlinarith
      | none =>
        simp only [potential, hs₁] at hΨ ⊢
        push_cast at hΨ ⊢
        nlinarith
    · simp only [potential, hs₁] at hΨ ⊢
      push_cast at hΨ ⊢
      nlinarith
  | delete x =>
    simp only [Op.Valid] at valid
    have hs₁ := bstDelete_size s.1 x valid
    have sp := (bstDelete_splice s.1 x valid).1
    have hy : deleteTarget s.1 x < s.1.size := by
      have := sp.size; simpa using this.2
    have hdy := he _ hy
    have hdy' : (s.1.depth (deleteTarget s.1 x) : ℚ) ≤ e := by exact_mod_cast hdy
    have hφ₁ : (phi (bstDelete s.1 x) : ℚ) ≤ phi s.1 + s.1.depth (deleteTarget s.1 x) := by
      have := phi_splice sp; simp only [unit_erase] at this; exact_mod_cast this
    have hpos : 0 < s.1.size := by omega
    simp only [step]
    split
    · rename_i hsmall
      have hc := rebuild_cost (bstDelete s.1 x)
      have hc' : ((rebuild (bstDelete s.1 x)).2 : ℚ) ≤ 2 * (bstDelete s.1 x).size := by exact_mod_cast hc
      -- `L (N - n') ≥ 2 n'` because `n' < α N`.
      have hpayL : 2 * ((bstDelete s.1 x).size : ℚ) ≤ L * (s.2 - (bstDelete s.1 x).size) := by
        rw [hLdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; nlinarith
      have hsz : ((bstDelete s.1 x).size : ℚ) = s.1.size - 1 := by rw [hs₁]; push_cast [Nat.cast_sub hpos]; ring
      simp only [potential, phi_rebuild, rebuild_size]
      push_cast
      rw [hsz] at hpayL hc'
      nlinarith
    · simp only [potential]
      have hsz : ((bstDelete s.1 x).size : ℚ) = s.1.size - 1 := by rw [hs₁]; push_cast [Nat.cast_sub hpos]; ring
      rw [hsz]
      push_cast
      nlinarith

end RotationBST.Classical.Scapegoat
