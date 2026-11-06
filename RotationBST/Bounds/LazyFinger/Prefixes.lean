module

public import RotationBST.Bounds.LazyFinger.Initialization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem costFrom_append (t : Tree) (p : Nat) (xs ys : List Nat) :
    costFrom t p (xs ++ ys) = costFrom t p xs + costFrom t (xs.getLastD p) ys := by
  induction xs generalizing p with
  | nil => simp [costFrom]
  | cons x xs ih => simp only [List.cons_append, costFrom, ih, List.getLastD_cons]; omega

/-- Appending requests cannot lower the cost in a fixed lazy-finger tree. -/
theorem cost_le_append (t : Tree) (xs ys : List Nat) : cost t xs ≤ cost t (xs ++ ys) := by
  cases t with
  | nil => simp [cost]
  | node l r => change costFrom _ _ xs ≤ costFrom _ _ (xs ++ ys); rw [costFrom_append]; omega

/-- Every prefix has no greater cost than any longer prefix. -/
theorem cost_take_mono (t : Tree) (xs : List Nat) (lo hi : Nat) (ordered : lo ≤ hi) :
    cost t (xs.take lo) ≤ cost t (xs.take hi) := by
  have split : xs.take hi = xs.take lo ++ (xs.drop lo).take (hi - lo) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.take_add (l := xs) (i := lo) (j := hi - lo))
  rw [split]
  exact cost_le_append t _ _

/-- Restarting a contiguous segment at the root costs at most one linear
initialization beyond the charges it had within the original execution. -/
theorem cost_segment (t : Tree) (xs : List Nat) (lo hi : Nat) (ordered : lo ≤ hi)
    (valid : ∀ x ∈ xs, x < t.size) :
    cost t ((xs.drop lo).take (hi - lo)) ≤
      cost t (xs.take hi) - cost t (xs.take lo) + t.size := by
  have split : xs.take hi = xs.take lo ++ (xs.drop lo).take (hi - lo) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.take_add (l := xs) (i := lo) (j := hi - lo))
  rw [split]
  cases t with
  | nil => simp [cost, List.length_append]
  | node l r =>
    have root : l.size < (Tree.node l r).size := by simp [Tree.size]; omega
    have last : (xs.take lo).getLastD l.size < (Tree.node l r).size := by
      have member := List.getLastD_mem_cons (l := xs.take lo) (a := l.size)
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using root
      · exact valid _ (List.mem_of_mem_take member)
    have bound := (initialization_bounds (.node l r) ((xs.take lo).getLastD l.size)
      ((xs.drop lo).take (hi - lo)) last
      (by intro x member; exact valid x (List.mem_of_mem_drop (List.mem_of_mem_take member)))).2
    simp only [cost, costFrom_append] at bound ⊢
    omega

end RotationBST.LazyFinger
