import TreeReset

/-! Composition facts for competitive bounds and reset arguments. -/
namespace RotationBST

theorem Execution.append (h : Execution s xs t k) (g : Execution t ys u m) :
    Execution s (xs ++ ys) u (k + m) := by
  induction h with
  | nil => simpa using g
  | cons ha _ ih =>
      simpa only [List.cons_append, Nat.add_assoc] using Execution.cons ha (ih g)

theorem Execution.size_eq (h : Execution s xs t k) : s.size = t.size := by
  induction h with
  | nil => rfl
  | cons ha _ ih => exact ha.1.size_eq.trans ih

theorem Execution.validInput (h : Execution s xs t k) : ValidInput s xs := by
  induction h with
  | nil => simp [ValidInput]
  | cons ha _ ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha.in_range
      · rw [ha.1.size_eq]; exact ih x hx

/-- Prefix a reset to a nonempty execution; its first access pays the reset. -/
theorem Execution.prepend_rotations (h : Execution t xs u k)
    (hr : Rotations s t j) (hne : xs ≠ []) : Execution s xs u (j + k) := by
  cases h with
  | nil => exact (hne rfl).elim
  | cons ha ht =>
      simpa only [Nat.add_assoc] using
        Execution.cons (show Access s _ _ _ from ⟨hr.append ha.1, ha.2⟩) ht

theorem StatefulAlgorithm.runFrom_append (a : StatefulAlgorithm σ)
    (q : σ) (t : Tree) (xs ys : List Nat) :
    a.runFrom q t (xs ++ ys) =
      let r := a.runFrom q t xs
      let z := a.runFrom r.1 r.2.1 ys
      (z.1, z.2.1, r.2.2 + z.2.2) := by
  induction xs generalizing q t with
  | nil => simp [StatefulAlgorithm.runFrom]
  | cons x xs ih => simp [StatefulAlgorithm.runFrom, ih, Nat.add_assoc]

theorem treeOnly_cost_eq (b : TreeAlgorithm) (s : Tree) (xs : List Nat) :
    b.totalCost s xs = xs.length + (b.runFrom () s xs).2.2 := by
  have hi : b.init s = () := Subsingleton.elim _ _
  simp [StatefulAlgorithm.totalCost, hi]

theorem treeOnly_cost_append (b : TreeAlgorithm) (s : Tree) (xs ys : List Nat) :
    b.totalCost s (xs ++ ys) = b.totalCost s xs +
      b.totalCost (b.runFrom () s xs).2.1 ys := by
  simp only [treeOnly_cost_eq, List.length_append, StatefulAlgorithm.runFrom_append]
  have hq : (b.runFrom () s xs).1 = () := Subsingleton.elim _ _
  simp only [hq]
  omega

theorem treeOnly_cost_cons (b : TreeAlgorithm) (s : Tree) (x : Nat) (xs : List Nat) :
    b.totalCost s (x :: xs) = 1 + (b.step () s x).2.2 +
      b.totalCost (b.step () s x).2.1 xs := by
  rcases he : b.step () s x with ⟨q, u, k⟩
  cases q
  rcases hr : b.runFrom () u xs with ⟨q', v, m⟩
  simp only [treeOnly_cost_eq, List.length_cons, StatefulAlgorithm.runFrom, he, hr]
  omega

/-- A competitive allowance for a common initial tree also bounds comparisons
against any other equal-size offline initial tree, with one extra reset. -/
theorem competitive_change_start (b : TreeAlgorithm) (C : Nat) (f : Nat → Nat)
    (bound : ∀ s xs u k, Execution s xs u k →
      b.totalCost s xs ≤ C * (xs.length + k) + f s.size)
    (s t : Tree) (hs : s.size = t.size) (h : Execution t xs u k) :
    b.totalCost s xs ≤ C * (xs.length + k) + (f s.size + C * (2 * s.size)) := by
  by_cases he : xs = []
  · subst xs
    simp [StatefulAlgorithm.totalCost, StatefulAlgorithm.runFrom]
  · obtain ⟨j, hj, hr⟩ := reset_linear s t hs
    have hb := bound s xs u (j + k) (h.prepend_rotations hr he)
    have hm := Nat.mul_le_mul_left C hj
    simp only [Nat.mul_add] at *
    omega

end RotationBST
