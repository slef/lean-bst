module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem balancedShape_valid (n : Nat) : (balancedShape n).Valid := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact (Multiway.Join.run_balance ih Balanced.nil).1

theorem balancedShape_size (n : Nat) : (balancedShape n).tree.size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have sizeEq := Multiway.Join.run_size (balancedShape n).height 0 (balancedShape n).tree .nil
    simp only [size, Nat.add_zero, ih] at sizeEq
    exact sizeEq

theorem initialInterval_valid (n : Nat) : IntervalValid (initialInterval n) := by
  cases n with
  | zero => trivial
  | succ n => exact fromRoot_valid (balancedShape_valid (n + 1))

theorem initialInterval_size (n : Nat) : (intervalTree (initialInterval n)).size = n := by
  cases n with
  | zero => rfl
  | succ n =>
    have nonempty : (balancedShape (n + 1)).tree ≠ .nil := by
      intro empty
      have sizes := balancedShape_size (n + 1)
      rw [empty, size] at sizes
      omega
    have steps := fromRoot_rotations (balancedShape (n + 1)).height (balancedShape (n + 1)).tree nonempty
    have sizes := steps.size_eq
    rw [binary_size, balancedShape_size] at sizes
    exact sizes.symm

/-- Any starting key-only shape can be initialized in at most two rotations
per key. The target is computed without using future touches. -/
theorem initialInterval_rotations (shape : Tree) :
    ∃ cost, cost ≤ 2 * shape.size ∧
      Rotations shape (intervalTree (initialInterval shape.size)) cost :=
  reset_linear shape _ (initialInterval_size shape.size).symm

/-- Creation pays once for reshaping and for the interval's entire future
splitting budget. This is charged in supernode keys, not gap-subtree sizes. -/
theorem initialInterval_budget (shape : Tree) :
    ∃ cost, Rotations shape (intervalTree (initialInterval shape.size)) cost ∧
      cost + intervalCredit (initialInterval shape.size) ≤ 6016 * shape.size := by
  obtain ⟨cost, bound, steps⟩ := initialInterval_rotations shape
  have credit := intervalCredit_linear (initialInterval shape.size)
  rw [initialInterval_size] at credit
  exact ⟨cost, steps, by omega⟩

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
