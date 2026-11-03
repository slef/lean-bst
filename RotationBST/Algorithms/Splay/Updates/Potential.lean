module

public import RotationBST.Algorithms.Splay.Updates.Basic
public import RotationBST.Algorithms.Splay.StaticOptimality

@[expose] public section

namespace RotationBST.Splay.Updates

/-- Unit-weight potential; no analysis weights change during updates. -/
noncomputable def unitPotential (t : Tree) : ℝ := potential (fun _ => 1) t 0

theorem potential_unit_offset (t : Tree) (lo : Nat) :
    potential (fun _ => 1) t lo = potential (fun _ => 1) t 0 := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp only [potential, mass_unit, il, ir]

theorem unitPotential_node (l r : Tree) :
    unitPotential (.node l r) = unitPotential l + unitPotential r + Real.logb 2 (Tree.node l r).size := by
  simp only [unitPotential, potential, mass_unit, potential_unit_offset]

theorem unitPotential_nil : unitPotential .nil = 0 := rfl

theorem unitPotential_nonneg (t : Tree) : 0 ≤ unitPotential t := by
  induction t with
  | nil => exact le_rfl
  | node l r il ir =>
      rw [unitPotential_node]
      linarith [Bounds.logb_nat_nonneg (Tree.node l r).size]

theorem unitPotential_upper (t : Tree) : unitPotential t ≤ (t.size : ℝ) * Real.logb 2 t.size :=
  potential_upper (fun _ => 1) (by intro; norm_num) t 0 t.size (by rw [mass_unit])

theorem log_nat_mono {a b : Nat} (h : a ≤ b) : Real.logb 2 a ≤ Real.logb 2 b := by
  by_cases ha : a = 0
  · subst a; simpa using Bounds.logb_nat_nonneg b
  · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero ha)
      (by exact_mod_cast h)

theorem unit_access (t : Tree) (x : Nat) (hx : x < t.size) :
    ((run t x).2 : ℝ) + unitPotential (run t x).1 - unitPotential t ≤
      3 * Real.logb 2 t.size + 1 := by
  simpa only [unitPotential, mass_unit, Real.logb_one, sub_zero] using
    access_lemma (fun _ => 1) (by intro; norm_num) t x hx

/-- Cutting the root's right edge cannot increase total forest potential. -/
theorem split_bound (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    ((split t k).cost : ℝ) + unitPotential (split t k).left +
      unitPotential (split t k).right - unitPotential t ≤ 3 * Real.logb 2 t.size + 1 := by
  by_cases h : k = 0
  · subst k
    simp only [split, ite_true, Nat.cast_zero, unitPotential_nil, zero_add, sub_self]
    linarith [Bounds.logb_nat_nonneg t.size]
  · have hx : k - 1 < t.size := by omega
    have ha := (run_correct t (k - 1) hx).1
    have hb := unit_access t (k - 1) hx
    rcases he : run t (k - 1) with ⟨u, c⟩
    rw [he] at ha hb
    cases u with
    | nil => exact ha.2.elim
    | node l r =>
        have hs := ha.1.size_eq
        have hm := log_nat_mono (show (Tree.node l .nil).size ≤ (Tree.node l r).size by simp [Tree.size])
        simp only [split, ite_eq_right h, he, unitPotential_node, unitPotential_nil, add_zero]
        rw [unitPotential_node] at hb
        dsimp only at hb
        linarith

/-- Joining adds only the root mass change to a maximum access in the left tree. -/
theorem join_bound (l r : Tree) :
    ((join l r).2 : ℝ) + unitPotential (join l r).1 - unitPotential l - unitPotential r ≤
      3 * Real.logb 2 (l.size + r.size : Nat) + 1 := by
  cases l with
  | nil =>
      simp only [join, Nat.cast_zero, zero_add, unitPotential_nil, sub_zero, sub_self, Tree.size]
      linarith [Bounds.logb_nat_nonneg r.size]
  | node a b =>
      obtain ⟨u, c, he, ha⟩ := run_max (.node a b) (by simp)
      have hx : (Tree.node a b).size - 1 < (Tree.node a b).size := by simp [Tree.size]
      have hb := unit_access (.node a b) ((Tree.node a b).size - 1) hx
      rw [he] at hb
      have hs := ha.1.size_eq
      have hs' : (Tree.node u r).size = (Tree.node a b).size + r.size := by
        simp only [Tree.size] at *; omega
      have hm := log_nat_mono (show (Tree.node a b).size ≤ (Tree.node a b).size + r.size by omega)
      simp only [join, he, unitPotential_node]
      rw [hs']
      rw [unitPotential_node, unitPotential_nil, add_zero, ← hs] at hb
      rw [unitPotential_node] at hb
      dsimp only at hb
      linarith

theorem insert_bound (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    ((insert t k).2 : ℝ) + unitPotential (insert t k).1 - unitPotential t ≤
      4 * Real.logb 2 (t.size + 1 : Nat) + 1 := by
  have hb := split_bound t k hk
  have hs := insert_size t k hk
  have hm := log_nat_mono (show t.size ≤ t.size + 1 by omega)
  simp only [insert, unitPotential_node]
  change (Tree.node (split t k).left (split t k).right).size = t.size + 1 at hs
  rw [hs]
  linarith

theorem delete_bound (t : Tree) (x : Nat) (hx : x < t.size) :
    ((delete t x).2 : ℝ) + unitPotential (delete t x).1 - unitPotential t ≤
      5 * Real.logb 2 t.size + 2 := by
  have ha := (run_correct t x hx).1
  have hb := unit_access t x hx
  rcases he : run t x with ⟨u, c⟩
  rw [he] at ha hb
  cases u with
  | nil => exact ha.2.elim
  | node l r =>
      have hj := join_bound l r
      have hs := ha.1.size_eq
      have hm := log_nat_mono (show l.size + r.size ≤ t.size by simp only [Tree.size] at hs; omega)
      rw [unitPotential_node, ← hs] at hb
      simp only [delete, he, Nat.cast_add]
      dsimp only at hb
      linarith

end RotationBST.Splay.Updates
