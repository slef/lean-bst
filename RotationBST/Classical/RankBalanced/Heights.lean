module

public import RotationBST.Classical.RankBalanced.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Real.GoldenRatio
public import RotationBST.Bounds.Implications.LogSum
import Mathlib.Tactic

@[expose] public section

/-! Heights and ranks of rank-balanced trees. Heights count nodes
(`Tree.height`); sizes are those of the underlying shape. -/
namespace RotationBST.Classical.RankBalanced
open _root_.RotationBST.Tree (height)

@[simp] theorem rank_node (l r : RankedTree) (k : Int) : rank (.node l k r) = k := rfl

@[simp] theorem rank_nil : rank .nil = -1 := rfl

theorem rank_ge (rule : Rule) (t : RankedTree) (h : Valid rule t) : -1 ≤ rank t := by
  cases t with
  | nil => simp [rank]
  | node l k r => have := h.1; simp only [rank_node]; omega

theorem rank_nil_iff (rule : Rule) (t : RankedTree) (h : Valid rule t) : rank t = -1 ↔ t = .nil := by
  cases t with
  | nil => simp [rank]
  | node l k r => have := h.1; simp only [rank_node, reduceCtorEq, iff_false]; omega

theorem size_node (l r : RankedTree) (k : Int) :
    (LabelledTree.node l k r).erase.size = l.erase.size + 1 + r.erase.size := rfl

theorem height_node (l r : RankedTree) (k : Int) :
    height (LabelledTree.node l k r).erase = max (height l.erase) (height r.erase) + 1 :=
  Nat.add_comm 1 _

/-! ### AVL trees -/

theorem avl_height_rank (t : RankedTree) (h : Valid .avl t) : (height t.erase : Int) = rank t + 1 := by
  induction t with
  | nil => simp [height, rank, LabelledTree.erase]
  | node l k r il ir =>
    obtain ⟨_, hloc, hl, hr⟩ := h
    have el := il hl
    have er := ir hr
    rw [height_node]
    simp only [rank_node, Rule.Local] at hloc ⊢
    push_cast
    omega

theorem avl_pow_height (t : RankedTree) (h : Valid .avl t) :
    Real.goldenRatio ^ height t.erase ≤ t.erase.size + 1 := by
  induction t with
  | nil => simp [height, LabelledTree.erase, Tree.size]
  | node l k r il ir =>
    have hv := h
    obtain ⟨_, hloc, hl, hr⟩ := h
    have pl := il hl
    have pr := ir hr
    have el := avl_height_rank l hl
    have er := avl_height_rank r hr
    simp only [Rule.Local] at hloc
    rw [height_node, size_node]
    push_cast
    have hφ := Real.one_lt_goldenRatio
    have hφ2 := Real.goldenRatio_lt_two
    -- The two child heights differ by at most one.
    have hd : height l.erase ≤ height r.erase + 1 ∧ height r.erase ≤ height l.erase + 1 := by omega
    rcases le_total (height l.erase) (height r.erase) with hle | hle
    · rw [max_eq_right hle]
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · rw [← heq] at pr ⊢
        have : Real.goldenRatio ^ (height l.erase + 1) ≤ 2 * Real.goldenRatio ^ height l.erase := by
          rw [pow_succ]; nlinarith [pow_pos (by linarith : (0:ℝ) < Real.goldenRatio) (height l.erase)]
        linarith
      · have hr1 : height r.erase = height l.erase + 1 := by omega
        rw [hr1] at pr ⊢
        have := Real.goldenRatio_pow_sub_goldenRatio_pow (height l.erase)
        linarith
    · rw [max_eq_left hle]
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · rw [← heq] at pl ⊢
        have : Real.goldenRatio ^ (height r.erase + 1) ≤ 2 * Real.goldenRatio ^ height r.erase := by
          rw [pow_succ]; nlinarith [pow_pos (by linarith : (0:ℝ) < Real.goldenRatio) (height r.erase)]
        linarith
      · have hl1 : height l.erase = height r.erase + 1 := by omega
        rw [hl1] at pl ⊢
        have := Real.goldenRatio_pow_sub_goldenRatio_pow (height r.erase)
        linarith

theorem avl_height (t : RankedTree) (h : Valid .avl t) :
    (height t.erase : ℝ) ≤ Real.logb Real.goldenRatio (t.erase.size + 1) := by
  rw [Real.le_logb_iff_rpow_le Real.one_lt_goldenRatio (by positivity), Real.rpow_natCast]
  exact avl_pow_height t h

theorem avl_wavl (t : RankedTree) (h : Valid .avl t) : Valid .wavl t := by
  induction t with
  | nil => trivial
  | node l k r il ir =>
    obtain ⟨hk, hloc, hl, hr⟩ := h
    refine ⟨hk, ?_, il hl, ir hr⟩
    simp only [Rule.Local] at hloc ⊢
    refine ⟨by omega, by omega, fun h1 h2 => ?_⟩
    subst h1; subst h2
    simp only [rank_nil] at hloc; omega

/-! ### Red-black trees -/

theorem redBlack_size (t : RankedTree) (h : Valid .redBlack t) :
    2 ^ (rank t + 1).toNat ≤ t.erase.size + 1 := by
  induction t with
  | nil => simp [rank, LabelledTree.erase, Tree.size]
  | node l k r il ir =>
    obtain ⟨hk, hloc, hl, hr⟩ := h
    have pl := il hl
    have pr := ir hr
    simp only [Rule.Local] at hloc
    rw [size_node]
    simp only [rank_node] at hloc ⊢
    have ml : 2 ^ k.toNat ≤ 2 ^ (rank l + 1).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    have mr : 2 ^ k.toNat ≤ 2 ^ (rank r + 1).toNat := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show (k + 1).toNat = k.toNat + 1 by omega, pow_succ]
    omega

theorem redBlack_height_aux (t : RankedTree) (h : Valid .redBlack t) :
    (height t.erase : Int) ≤ 2 * (rank t + 1) ∧
      (NoZeroChild t → t ≠ .nil → (height t.erase : Int) ≤ 2 * rank t + 1) := by
  induction t with
  | nil => simp [height, rank, LabelledTree.erase]
  | node l k r il ir =>
    obtain ⟨hk, hloc, hl, hr⟩ := h
    obtain ⟨al, bl⟩ := il hl
    obtain ⟨ar, br⟩ := ir hr
    obtain ⟨dl, dr, zl, zr⟩ := hloc
    have nl := rank_nil_iff .redBlack l hl
    have nr := rank_nil_iff .redBlack r hr
    simp only [rank_node] at dl dr zl zr ⊢
    rw [height_node]
    -- A 0-child has rank `k`, is a node, and has no 0-child.
    have cl : (height l.erase : Int) ≤ 2 * k + 1 := by
      rcases dl with d | d
      · exact (bl (zl d) (fun e => by rw [← nl] at e; omega)).trans (by omega)
      · omega
    have cr : (height r.erase : Int) ≤ 2 * k + 1 := by
      rcases dr with d | d
      · exact (br (zr d) (fun e => by rw [← nr] at e; omega)).trans (by omega)
      · omega
    refine ⟨by push_cast; omega, fun hz _ => ?_⟩
    simp only [NoZeroChild] at hz
    push_cast; omega

theorem redBlack_height (t : RankedTree) (h : Valid .redBlack t) :
    (height t.erase : ℝ) ≤ 2 * Real.logb 2 (t.erase.size + 1) := by
  have h1 := (redBlack_height_aux t h).1
  have h2 := Bounds.le_logb_of_pow _ _ (redBlack_size t h)
  have hr := rank_ge .redBlack t h
  push_cast at h2
  have : (height t.erase : ℝ) ≤ 2 * ((rank t + 1).toNat : ℝ) := by
    have : (height t.erase : Int) ≤ 2 * ((rank t + 1).toNat : Int) := by omega
    exact_mod_cast this
  linarith

/-! ### WAVL trees -/

theorem wavl_size (t : RankedTree) (h : Valid .wavl t) :
    2 ^ (rank t + 1).toNat ≤ (t.erase.size + 1) ^ 2 := by
  induction t with
  | nil => simp [rank, LabelledTree.erase, Tree.size]
  | node l k r il ir =>
    obtain ⟨hk, hloc, hl, hr⟩ := h
    have pl := il hl
    have pr := ir hr
    have gl := rank_ge .wavl l hl
    have gr := rank_ge .wavl r hr
    obtain ⟨dl, dr, _⟩ := hloc
    simp only [rank_node] at dl dr ⊢
    rw [size_node]
    set a := l.erase.size + 1
    set b := r.erase.size + 1
    have X : 2 ^ (k - 1).toNat ≤ a ^ 2 ∧ 2 ^ (k - 1).toNat ≤ b ^ 2 :=
      ⟨(Nat.pow_le_pow_right (by norm_num) (by omega)).trans pl,
        (Nat.pow_le_pow_right (by norm_num) (by omega)).trans pr⟩
    have hab : 2 ^ (k - 1).toNat ≤ a * b := by
      rcases le_total a b with hle | hle
      · exact X.1.trans (by rw [pow_two]; exact Nat.mul_le_mul_left a hle)
      · exact X.2.trans (by rw [pow_two]; exact Nat.mul_le_mul_right b hle)
    have hsq : (a + 1 + r.erase.size) = a + b := by simp only [b]; omega
    rw [show l.erase.size + 1 + r.erase.size + 1 = a + b by simp only [a, b]; omega]
    have e : (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
    rw [e]
    by_cases hk0 : k = 0
    · subst hk0
      have ha : 1 ≤ a := by simp only [a]; omega
      have hb : 1 ≤ b := by simp only [b]; omega
      simp; nlinarith
    · rw [show (k + 1).toNat = (k - 1).toNat + 2 by omega, pow_add]
      nlinarith [X.1, X.2]

theorem wavl_rank (t : RankedTree) (h : Valid .wavl t) :
    (rank t : ℝ) + 1 ≤ 2 * Real.logb 2 (t.erase.size + 1) := by
  have hs := Bounds.le_logb_of_pow _ _ (wavl_size t h)
  have hr := rank_ge .wavl t h
  push_cast at hs
  rw [Real.logb_pow] at hs
  norm_num at hs
  have : (rank t : ℝ) + 1 = ((rank t + 1).toNat : ℝ) := by
    have : rank t + 1 = ((rank t + 1).toNat : Int) := by omega
    exact_mod_cast this
  linarith

theorem wavl_height_rank (t : RankedTree) (h : Valid .wavl t) : (height t.erase : Int) ≤ rank t + 1 := by
  induction t with
  | nil => simp [height, rank, LabelledTree.erase]
  | node l k r il ir =>
    obtain ⟨_, hloc, hl, hr⟩ := h
    have el := il hl
    have er := ir hr
    obtain ⟨dl, dr, _⟩ := hloc
    rw [height_node]
    simp only [rank_node] at dl dr ⊢
    push_cast; omega

theorem wavl_height (t : RankedTree) (h : Valid .wavl t) :
    (height t.erase : ℝ) ≤ 2 * Real.logb 2 (t.erase.size + 1) := by
  have h1 := wavl_height_rank t h
  have h2 := wavl_rank t h
  have : (height t.erase : ℝ) ≤ (rank t : ℝ) + 1 := by exact_mod_cast h1
  linarith

end RotationBST.Classical.RankBalanced
