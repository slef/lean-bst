import RotationBST
open RotationBST
open Tree

private def leaf : Tree := .node .nil .nil
private def two : Tree := .node leaf .nil
private def promoted : Tree := .node .nil leaf

-- Rank 0 becomes root in one rotation; rank 1 is already the root.
example : Access two promoted 0 1 := ⟨.step .right .refl, rfl⟩
example : Access two two 1 0 := ⟨.refl, rfl⟩
example : ¬ Access two .nil x k := fun h => h.2
example : ¬ Access two t 2 k := by
  intro h
  have := h.in_range
  change 2 < 2 at this
  omega

-- A rotation deep inside a subtree still costs exactly one.
example : Rotations (.node leaf two) (.node leaf promoted) 1 :=
  .step (.inRight .right) .refl

-- A complete two-request execution.
example : Execution two [0, 1] two 2 :=
  .cons ⟨.step .right .refl, rfl⟩
    (.cons ⟨.step .left .refl, rfl⟩ .nil)

example : workingSetNumber 5 [] 2 = 5 := by decide
example : workingSetNumber 5 [2] 2 = 1 := by decide
example : workingSetNumber 5 [2, 0, 1, 0] 2 = 3 := by decide

-- The online rule produces a legal offline execution on every valid input.
example (a : Algorithm) (past : List Nat) (t : Tree) (xs : List Nat)
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

#print axioms Rotate.size_eq
#print axioms Access.in_range
