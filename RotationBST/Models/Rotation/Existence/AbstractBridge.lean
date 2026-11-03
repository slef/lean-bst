module

public import RotationBST.Algorithms.MoveToRoot.Algorithm

@[expose] public section

namespace RotationBST.AccessBridge

variable {t u : Tree} {xs : List Nat} {k : Nat}

theorem exists_iff (t : Tree) (x : Nat) :
    (∃ u k, Access t u x k ∧ k < t.size) ↔ x < t.size := by
  constructor
  · rintro ⟨u, k, ha, _⟩
    exact ha.in_range
  · intro hx
    exact ⟨_, _, moveToRoot_correct t x hx⟩

theorem run_execution (a : Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    Execution t xs (a.runFrom past t xs).1 (a.runFrom past t xs).2 := by
  induction xs generalizing past t with
  | nil => exact .nil
  | cons x xs ih =>
    have ha := a.correct past t x (valid x (by simp))
    have hv : ∀ y ∈ xs, y < (a.step past t x).1.size := by
      intro y hy
      rw [← ha.1.size_eq]
      exact valid y (by simp [hy])
    exact .cons ha (ih (past ++ [x]) (a.step past t x).1 hv)

theorem execution_valid (h : Execution t xs u k) : ∀ x ∈ xs, x < t.size := by
  induction h with
  | nil => simp
  | cons ha _ ih =>
      intro y hy
      rcases List.mem_cons.mp hy with h | h
      · subst y; exact ha.in_range
      · rw [ha.1.size_eq]; exact ih y h

theorem execution_iff (t : Tree) (xs : List Nat) :
    (∃ u k, Execution t xs u k) ↔ ∀ x ∈ xs, x < t.size := by
  constructor
  · rintro ⟨u, k, h⟩; exact execution_valid h
  · intro h
    exact ⟨_, _, run_execution moveToRootAlgorithm [] t xs h⟩

end RotationBST.AccessBridge
